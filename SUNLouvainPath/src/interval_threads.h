#ifndef SUNLOUVAINPATH_INTERVAL_THREADS_H
#define SUNLOUVAINPATH_INTERVAL_THREADS_H

#include <Rcpp.h>
#include <algorithm>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <exception>
#include <mutex>
#include <optional>
#include <stdexcept>
#include <thread>
#include <utility>
#include <vector>

namespace interval_threads {
// Only the calling R thread may check R interrupts. Worker threads poll this
// call's cancellation flag between sweeps and resolution boundaries instead.
inline thread_local const std::atomic<bool>* cancel_flag = nullptr;
}

inline void poll_path_interrupt() {
    if (interval_threads::cancel_flag == nullptr) {
        Rcpp::checkUserInterrupt();
    } else if (interval_threads::cancel_flag->load()) {
        throw std::runtime_error("Interval enumeration cancelled");
    }
}

template<class F>
auto map_intervals(std::size_t count, int workers, F evaluate)
        -> std::vector<decltype(evaluate(std::size_t{}))> {
    using Result = decltype(evaluate(std::size_t{}));
    std::vector<Result> ordered;
    ordered.reserve(count);
    if (workers <= 1 || count <= 1) {
        for (std::size_t i = 0; i < count; ++i) ordered.push_back(evaluate(i));
        return ordered;
    }

    const std::size_t thread_count = std::min(count, static_cast<std::size_t>(workers));
    std::vector<std::optional<Result>> results(count);
    std::vector<std::thread> pool;
    pool.reserve(thread_count);
    std::atomic<std::size_t> next{0};
    std::atomic<bool> cancel{false};
    std::mutex mutex;
    std::condition_variable cv;
    std::size_t finished = 0;
    std::exception_ptr worker_failure;

    auto work = [&]() {
        interval_threads::cancel_flag = &cancel;
        try {
            while (!cancel.load()) {
                const std::size_t i = next.fetch_add(1);
                if (i >= count) break;
                results[i].emplace(evaluate(i));
            }
        } catch (...) {
            std::lock_guard<std::mutex> lock(mutex);
            if (!worker_failure) worker_failure = std::current_exception();
            cancel.store(true);
        }
        interval_threads::cancel_flag = nullptr;
        {
            std::lock_guard<std::mutex> lock(mutex);
            ++finished;
        }
        cv.notify_one();
    };
    std::exception_ptr caller_failure;
    try {
        for (std::size_t i = 0; i < thread_count; ++i) pool.emplace_back(work);
        for (;;) {
            std::unique_lock<std::mutex> lock(mutex);
            if (cv.wait_for(lock, std::chrono::milliseconds(100),
                            [&]() { return finished == thread_count; })) break;
            lock.unlock();
            Rcpp::checkUserInterrupt();
        }
    } catch (...) {
        caller_failure = std::current_exception();
        cancel.store(true);
    }
    for (auto& thread : pool) thread.join();
    if (caller_failure) std::rethrow_exception(caller_failure);
    if (worker_failure) std::rethrow_exception(worker_failure);
    // Use domain order, including for IDs and tied optima, regardless of
    // which job finished first.
    for (auto& item : results) ordered.push_back(std::move(item.value()));
    return ordered;
}

#endif
