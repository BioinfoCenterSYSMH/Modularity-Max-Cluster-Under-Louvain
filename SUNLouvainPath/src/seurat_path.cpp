#include "interval_threads.h"
#include "path_common.h"
#include "seurat_optimizer.h"
#include <cstdint>
#include <tuple>

namespace {
using namespace mml_path_common;

struct ScanResult {
    IntervalData path;
    std::uint64_t exact_runs = 0;
    std::uint64_t right_runs = 0;
};

// Each trace uses the same seed and replays the full set of starts. Thus a
// winning-start switch is a boundary even when no start changes its partition.
ScanResult scan(const mml_s55::Optimizer& optimizer, Rational current,
                const std::optional<Rational>& upper, bool include_upper) {
    ScanResult result;
    PartitionIndex index;
    auto identify = [&](Labels labels) {
        if (index.size() >= static_cast<std::size_t>(std::numeric_limits<int>::max())) {
            throw std::overflow_error("Too many distinct Seurat optimizer results for an R matrix");
        }
        return index.try_emplace(std::move(labels), static_cast<int>(index.size()) + 1).first->second;
    };
    auto at_point = [&]() {
        mml_s55::Trace point(current, false);
        ++result.exact_runs;
        return identify(optimizer.run(point));
    };

    for (;;) {
        poll_path_interrupt();
        const std::string here = current.str();
        if (upper && current == *upper) {
            if (include_upper) append(result.path.segments, at_point(), here, here, true, true);
            break;
        }

        mml_s55::Trace right(current, true);
        ++result.right_runs;
        Labels right_labels = optimizer.run(right);
        // IDs follow the order of first appearance: isolated point first,
        // then the open interval following it.
        const int exact_id = right.differs_at_start ? at_point() : 0;
        const int open_id = identify(std::move(right_labels));
        append(result.path.segments, exact_id ? exact_id : open_id, here, here, true, true);

        const auto next = right.next();
        if (upper && (!next || *upper <= *next)) {
            const bool stable_at_end = !next || *upper < *next;
            append(result.path.segments, open_id, here, upper->str(), false,
                   include_upper && stable_at_end);
            if (include_upper && !stable_at_end) {
                current = *upper;
                append(result.path.segments, at_point(), upper->str(), upper->str(), true, true);
            }
            break;
        }
        append(result.path.segments, open_id, here, next ? next->str() : "Inf", false, false);
        if (!next) break;
        current = *next;
    }
    result.path.partitions = take_partitions(index);
    return result;
}
} // namespace

// [[Rcpp::export(rng = false)]]
Rcpp::List seurat_path_cpp(int n, Rcpp::IntegerVector i, Rcpp::IntegerVector j,
                           Rcpp::IntegerVector type, Rcpp::NumericVector values,
                           Rcpp::NumericVector overlap, int k,
                           Rcpp::CharacterVector split_points, std::string r_max, int workers,
                           int algorithm, int modularity_fxn, int n_start, int n_iter,
                           int random_seed) {
    if (algorithm != 1 && algorithm != 2) Rcpp::stop("Seurat Louvain algorithm must be 1 or 2.");
    if (modularity_fxn != 1 && modularity_fxn != 2) Rcpp::stop("modularity.fxn must be 1 or 2.");
    if (workers < 1 || n_start < 1 || n_iter < 1) Rcpp::stop("workers, n.start and n.iter must be positive.");
    if (n < 1 || i.size() != j.size() || type.size() != i.size() || k < 0 ||
        (k && overlap.size() != values.size())) Rcpp::stop("Malformed Seurat graph encoding.");

    const auto encoding = encode_weights(values, overlap, k);
    std::vector<mml_s55::Edge> edges;
    edges.reserve(i.size());
    for (R_xlen_t e = 0; e < i.size(); ++e) {
        if ((e & 16383) == 0) poll_path_interrupt();
        if (i[e] < 1 || j[e] > n || i[e] >= j[e] || type[e] < 1 || type[e] > values.size()) {
            Rcpp::stop("Invalid Seurat optimizer edge or weight index.");
        }
        edges.push_back({i[e] - 1, j[e] - 1, encoding.weights[type[e] - 1]});
    }
    // FindClusters reads the lower triangle in compressed-column order.
    // Our R adapter supplies the upper triangle; recover the native visit
    // order of edges independently of input storage.
    std::sort(edges.begin(), edges.end(), [](const auto& a, const auto& b) {
        return std::tie(a.u, a.v) < std::tie(b.u, b.v);
    });
    mml_s55::Optimizer optimizer(n, edges, encoding.scale, algorithm, modularity_fxn,
                                 n_start, n_iter, random_seed);
    // The optimizer owns its immutable adjacency. Release this temporary
    // ordered edge list before allocating interval results.
    std::vector<mml_s55::Edge>().swap(edges);

    auto limit = upper_limit(r_max);
    if (modularity_fxn == 2 && (!limit || *limit > 1)) limit = Rational(1);
    auto starts = interior_splits(split_points, limit);
    Rcpp::CharacterVector splits(starts.size());
    for (std::size_t s = 0; s < starts.size(); ++s) splits[s] = starts[s].str();
    starts.insert(starts.begin(), Rational(0));
    const int used = static_cast<int>(std::min<std::size_t>(workers, starts.size()));
    auto scanned = map_intervals(starts.size(), used, [&](std::size_t s) {
        const bool last = s + 1 == starts.size();
        const auto end = last ? limit : std::optional<Rational>(starts[s+1]);
        return scan(optimizer, starts[s], end, last && limit.has_value());
    });

    std::vector<IntervalData> blocks;
    blocks.reserve(scanned.size());
    std::uint64_t exact_runs = 0, right_runs = 0;
    for (auto& part : scanned) {
        exact_runs += part.exact_runs;
        right_runs += part.right_runs;
        blocks.push_back(std::move(part.path));
    }
    auto path = merge_intervals(std::move(blocks));
    Rcpp::IntegerMatrix membership(n, path.partitions.size());
    for (std::size_t p = 0; p < path.partitions.size(); ++p) {
        poll_path_interrupt();
        for (int u = 0; u < n; ++u) membership(u, p) = path.partitions[p][u] + 1;
    }
    return Rcpp::List::create(
        Rcpp::_["membership"] = membership,
        Rcpp::_["intervals"] = interval_frame(path.segments),
        Rcpp::_["search_plan"] = Rcpp::List::create(
            Rcpp::_["mode"] = "seurat_exact_trace",
            Rcpp::_["scan_r_max"] = limit ? limit->str() : std::string("Inf"),
            Rcpp::_["scan_upper_closed"] = limit.has_value(),
            Rcpp::_["scan_split_points"] = splits,
            Rcpp::_["effective_workers"] = used,
            Rcpp::_["exact_point_runs"] = static_cast<double>(exact_runs),
            Rcpp::_["right_limit_runs"] = static_cast<double>(right_runs)));
}
