#ifndef MML_SEURAT_OPTIMIZER_H
#define MML_SEURAT_OPTIMIZER_H

// Exact-arithmetic adaptation of Seurat 5.5.0 src/ModularityOptimizer.cpp
// and src/RModularityOptimizer.cpp, based on the Java
// Modularity Optimizer by Ludo Waltman and Nees Jan van Eck.
// https://github.com/satijalab/seurat/tree/v5.5.0/src
//
// Original Seurat code: Copyright (c) 2021 Seurat authors. MIT License.
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.
#include "seurat_trace.h"
#include "interval_threads.h"
#include <algorithm>
#include <cstdint>
#include <numeric>
#include <stdexcept>
#include <utility>
#include <vector>

namespace mml_s55 {

class JavaRandom {
    static constexpr std::uint64_t multiplier = 0x5deece66dULL;
    static constexpr std::uint64_t mask = (1ULL << 48) - 1;
    std::uint64_t seed;

    std::uint32_t next31() {
        seed = (seed * multiplier + 11) & mask;
        return static_cast<std::uint32_t>(seed >> 17);
    }

    int next_int(int bound) {
        const auto n = static_cast<std::uint32_t>(bound);
        if ((n & (n - 1)) == 0)
            return static_cast<int>((static_cast<std::uint64_t>(n) * next31()) >> 31);
        std::uint32_t bits, value;
        do {
            bits = next31();
            value = bits % n;
            // Java tests the sign after a signed 32-bit addition. Unsigned
            // arithmetic gives the same rejection without signed overflow.
        } while (bits - value + (n - 1) >= (1U << 31));
        return static_cast<int>(value);
    }

public:
    explicit JavaRandom(int initial) : seed((static_cast<std::uint64_t>(initial) ^ multiplier) & mask) {}

    std::vector<int> permutation(int n) {
        std::vector<int> order(n);
        std::iota(order.begin(), order.end(), 0);
        // The original draws from [0,n) on every iteration, including the last.
        for (int i = 0; i < n; ++i) std::swap(order[i], order[next_int(n)]);
        return order;
    }
};

class Optimizer {
    using Labels = std::vector<int>;
    struct Arc { int neighbor; Integer weight; };
    struct Level {
        std::vector<std::vector<Arc>> adj;
        std::vector<Integer> mass;
        explicit Level(int n) : adj(n), mass(n) {}
        int size() const { return static_cast<int>(adj.size()); }
    };
    struct Clustering {
        Labels id;
        int count;
        explicit Clustering(int n) : id(n), count(n) { std::iota(id.begin(), id.end(), 0); }
    };
    struct Score {
        Integer observed, penalty;
    };
    Level original;
    // In the common integer gain, each edge sum is multiplied by edge_factor;
    // each product of cluster masses is multiplied by mass_factor and r.
    Integer edge_factor = 1, mass_factor = 1;
    int algorithm, starts, iterations, initial_seed;

    static Level collapse(const Level& level, const Clustering& clusters) {
        Level next(clusters.count);
        std::vector<Labels> members(clusters.count);
        for (int u = 0; u < level.size(); ++u) members[clusters.id[u]].push_back(u);
        std::vector<Integer> sums(clusters.count);
        Labels neighbors;
        for (int c = 0; c < clusters.count; ++c) {
            if ((c & 255) == 0) poll_path_interrupt();
            for (int u : members[c]) {
                next.mass[c] += level.mass[u];
                for (const auto& edge : level.adj[u]) {
                    const int d = clusters.id[edge.neighbor];
                    if (d == c) continue; // self links are constant in move comparisons
                    if (sums[d] == 0) neighbors.push_back(d);
                    sums[d] += edge.weight;
                }
            }
            // Seurat's reduced adjacency is in encounter order, not cluster ID order.
            for (int d : neighbors) {
                next.adj[c].push_back({d, std::move(sums[d])});
                sums[d] = 0;
            }
            neighbors.clear();
        }
        return next;
    }

    bool local_move(const Level& level, Clustering& clusters, JavaRandom& rng, Trace& trace) const {
        const int n = level.size();
        if (n == 1) return false;
        std::vector<Integer> mass(n), links(n);
        Labels population(n), unused, candidates;
        for (int u = 0; u < n; ++u) {
            ++population[clusters.id[u]];
            mass[clusters.id[u]] += level.mass[u];
        }
        for (int c = 0; c < n; ++c) if (population[c] == 0) unused.push_back(c);
        const Labels order = rng.permutation(n);
        int stable = 0, pos = 0;
        bool changed = false;
        do {
            if ((pos & 255) == 0) poll_path_interrupt();
            const int u = order[pos], from = clusters.id[u];
            for (const Arc& edge : level.adj[u]) {
                const int c = clusters.id[edge.neighbor];
                if (links[c] == 0) candidates.push_back(c);
                links[c] += edge.weight;
            }
            mass[from] -= level.mass[u];
            if (--population[from] == 0) unused.push_back(from);
            int best = -1;
            Integer winning_links = 0, winning_mass = 0;
            const Integer scaled_mass = level.mass[u] * mass_factor;
            for (int c : candidates) {
                const int comparison = trace.compare((links[c] - winning_links) * edge_factor,
                                                     (winning_mass - mass[c]) * scaled_mass);
                if (comparison > 0 || (comparison == 0 && c < best)) {
                    best = c;
                    winning_links = links[c];
                    winning_mass = mass[c];
                }
                links[c] = 0;
            }
            candidates.clear();
            if (best == -1) {
                // The zero baseline wins every tie with zero. A singleton
                // emptied on this visit is on top of the unused-cluster stack.
                best = unused.back();
                unused.pop_back();
            }
            mass[best] += level.mass[u];
            ++population[best];
            if (best == from) {
                ++stable;
            } else {
                clusters.id[u] = best;
                stable = 1;
                changed = true;
            }
            pos = (pos + 1 == n) ? 0 : pos + 1;
        } while (stable < n);

        Labels compact(n);
        clusters.count = 0;
        for (int c = 0; c < n; ++c) if (population[c]) compact[c] = clusters.count++;
        for (int& c : clusters.id) c = compact[c];
        return changed;
    }

    bool louvain(const Level& level, Clustering& clusters, JavaRandom& rng, Trace& trace) const {
        if (level.size() == 1) return false;
        bool changed = local_move(level, clusters, rng, trace);
        if (clusters.count < level.size()) {
            Level coarse = collapse(level, clusters);
            Clustering higher(coarse.size());
            if (louvain(coarse, higher, rng, trace)) {
                for (int& c : clusters.id) c = higher.id[c];
                clusters.count = higher.count;
                changed = true;
                if (algorithm == 2) local_move(level, clusters, rng, trace);
            }
        }
        return changed;
    }

    Score score(const Clustering& p) const {
        Integer within = 0, squares = 0;
        std::vector<Integer> mass(p.count);
        for (int u = 0; u < original.size(); ++u) {
            if ((u & 255) == 0) poll_path_interrupt();
            mass[p.id[u]] += original.mass[u];
            for (const auto& edge : original.adj[u])
                if (p.id[u] == p.id[edge.neighbor]) within += edge.weight;
        }
        for (const auto& x : mass) squares += x * x;
        return {within * edge_factor, squares * mass_factor};
    }

    static Labels order_by_size(Clustering& p) {
        Labels size(p.count), order(p.count), ids(p.count);
        for (int c : p.id) ++size[c];
        std::iota(order.begin(), order.end(), 0);
        std::stable_sort(order.begin(), order.end(), [&](int a, int b) { return size[a] > size[b]; });
        for (int i = 0; i < p.count; ++i) ids[order[i]] = i;
        for (int& c : p.id) c = ids[c];
        return std::move(p.id);
    }

public:
    Optimizer(int n, const std::vector<Edge>& edges, const Integer& unit, int algorithm,
              int modularity_fxn, int n_start, int n_iter, int random_seed)
        : original(n), algorithm(algorithm), starts(n_start), iterations(n_iter), initial_seed(random_seed) {
        if (n < 1 || starts < 1 || iterations < 1 || unit <= 0 ||
            (algorithm != 1 && algorithm != 2) || (modularity_fxn != 1 && modularity_fxn != 2))
            throw std::invalid_argument("Invalid Seurat Louvain optimizer configuration.");
        Integer total = 0;
        for (const auto& e : edges) {
            if (e.u < 0 || e.v >= n || e.u >= e.v || e.w <= 0)
                throw std::invalid_argument("Seurat optimizer requires positive undirected edges.");
            original.adj[e.u].push_back({e.v, e.w});
            original.adj[e.v].push_back({e.u, e.w});
            original.mass[e.u] += e.w;
            original.mass[e.v] += e.w;
            total += 2 * e.w;
        }
        if (modularity_fxn == 1) {
            edge_factor = std::move(total);
        } else {
            std::fill(original.mass.begin(), original.mass.end(), Integer(1));
            mass_factor = unit;
        }
    }

    Labels run(Trace& trace) const {
        JavaRandom rng(initial_seed);
        Clustering winner(original.size());
        Score best;
        for (int s = 0; s < starts; ++s) {
            Clustering candidate(original.size());
            for (int i = 0; i < iterations; ++i) {
                poll_path_interrupt();
                if (!louvain(original, candidate, rng, trace)) break;
            }
            Score value = score(candidate);
            // Each start's final score is an affine function of r throughout
            // its trace. A winner switch can occur even if no move changes.
            if (s == 0 || trace.compare(value.observed - best.observed, best.penalty - value.penalty) > 0) {
                best = std::move(value);
                winner = std::move(candidate);
            }
        }
        return order_by_size(winner);
    }
};

} // namespace mml_s55
#endif
