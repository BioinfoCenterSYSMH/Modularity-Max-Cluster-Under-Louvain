#ifndef SUNLOUVAINPATH_STRUCTURAL_H
#define SUNLOUVAINPATH_STRUCTURAL_H

// Included inside path.cpp's anonymous namespace, after the generic interval
// scanner. Every subgraph keeps the original integer weights and the same
// total (2W). Its comparisons therefore use the global resolution directly.
Labels canonical_structural_labels(Labels labels) {
    Labels ids(labels.size(), -1);
    int next = 0;
    for (int& label : labels) {
        if (ids[label] < 0) ids[label] = next++;
        label = ids[label];
    }
    return labels;
}

int next_structural_id(std::size_t count) {
    if (count >= static_cast<std::size_t>(std::numeric_limits<int>::max())) {
        throw std::length_error("The number of distinct partitions exceeds R's matrix column limit.");
    }
    return static_cast<int>(count) + 1;
}

struct PairBreakpoint {
    Rational resolution;
    Integer score_change;
    Labels split_vertices;
};

struct StructuralUnit {
    Labels vertices; // increasing original vertex indices
    Network graph;
    bool matching;
    Rational tail = 0;
    Integer singleton_score = 0, joined_score = 0;
    Labels joined_labels;
    std::vector<PairBreakpoint> breaks;

    StructuralUnit(Labels members, bool is_matching)
        : vertices(std::move(members)), graph(0), matching(is_matching) {}

    void prepare(const Integer& total) {
        const int n = static_cast<int>(vertices.size());
        if (matching) {
            joined_labels.resize(n);
            std::iota(joined_labels.begin(), joined_labels.end(), 0);
            // At equal weights all independent pairs split at the same
            // resolution. Initially identify each pair by its smaller vertex.
            std::map<Integer, Labels, std::greater<Integer>> groups;
            for (int u = 0; u < n; ++u) {
                if ((u & 1023) == 0) poll_path_interrupt();
                if (graph.adjacency[u].empty()) continue;
                const auto& [v, w] = *graph.adjacency[u].begin();
                if (v > u) {
                    joined_labels[v] = u;
                    groups[w].push_back(v);
                }
            }
            for (auto& [w, vertices_to_split] : groups) {
                const Integer count = vertices_to_split.size();
                const Integer w_squared = w * w;
                joined_score += count * (2 * total * w - 4 * w_squared);
                breaks.push_back({Rational(total, w), count * (2 * w_squared - 2 * total * w),
                                  std::move(vertices_to_split)});
            }
            if (!breaks.empty()) tail = breaks.back().resolution;
            graph = Network(0);
            return;
        }

        // The initial singleton state is locally stationary precisely when
        // r >= total * max_{edges}(w_uv / (d_u*d_v)). A strictly improving
        // move below this bound precludes returning to that initial state.
        Integer best_w = 0, best_product = 1;
        for (int u = 0; u < n; ++u) {
            if ((u & 255) == 0) poll_path_interrupt();
            const Integer& degree = graph.volume[u];
            singleton_score -= degree * degree;
            for (const auto& [v, w] : graph.adjacency[u]) {
                if (u >= v) continue;
                Integer product = degree * graph.volume[v];
                if (w * best_product > best_w * product) {
                    best_w = w;
                    best_product = std::move(product);
                }
            }
        }
        tail = Rational(total * best_w, best_product);
    }

    IntervalData scan_matching(const Rational& lower, const std::optional<Rational>& upper,
                               bool include_upper) const {
        Labels labels = joined_labels;
        Integer score = joined_score;
        auto split = [&](const PairBreakpoint& event) {
            for (int v : event.split_vertices) labels[v] = v;
            score += event.score_change;
        };
        auto event = breaks.begin();
        while (event != breaks.end() && event->resolution <= lower) split(*event++);

        IntervalData result;
        std::string start = lower.str();
        auto emit = [&](const std::string& end, bool right_closed) {
            poll_path_interrupt();
            int id = next_structural_id(result.partitions.size());
            result.partitions.push_back(canonical_structural_labels(labels));
            result.numerators.push_back(score);
            result.segments.push_back({id, start, end, true, right_closed});
        };
        for (; event != breaks.end(); ++event) {
            if (upper && (event->resolution > *upper ||
                         (event->resolution == *upper && !include_upper))) break;
            const std::string next = event->resolution.str();
            emit(next, false);
            split(*event);
            start = next;
        }
        emit(upper ? upper->str() : "Inf", upper && include_upper);
        return result;
    }

    IntervalData scan(const Integer& total, const Rational& lower,
                      const std::optional<Rational>& upper, bool include_upper) const {
        if (matching) return scan_matching(lower, upper, include_upper);
        if (upper && (*upper < tail || (*upper == tail && !include_upper))) {
            return scan_interval(graph, total, lower, upper, include_upper);
        }
        IntervalData result;
        if (lower < tail) result = scan_interval(graph, total, lower, tail, false);
        Labels singleton(vertices.size());
        std::iota(singleton.begin(), singleton.end(), 0);
        const int id = next_structural_id(result.partitions.size());
        result.partitions.push_back(std::move(singleton));
        result.numerators.push_back(singleton_score);
        result.segments.push_back({id, std::max(lower, tail).str(), upper ? upper->str() : "Inf",
                                   true, upper && include_upper});
        return result;
    }
};

class StructuralPlan {
    const Integer& total;
    const int cell_count;
    std::size_t edges = 0;
    Labels component_sizes;
    std::vector<StructuralUnit> units;
    Rational tail = 0;

    // All n-by-B global membership output is constructed once per distinct
    // tuple of local partition IDs. Scores sum the local contributions with
    // the common global (2W)^2 denominator.
    IntervalData compose(const std::vector<IntervalData>& paths, const std::optional<Rational>& upper,
                         bool include_upper) const {
        struct Change { std::size_t unit; int id; bool point, right; };
        std::map<Rational, std::vector<Change>> events;
        if (upper && include_upper) events[*upper];
        for (std::size_t c = 0; c < paths.size(); ++c) {
            for (const auto& s : paths[c].segments) {
                events[Rational(s.lower)].push_back({c, s.id, s.left_closed, s.lower != s.upper});
            }
        }

        IntervalData result;
        PartitionIndex combinations;
        auto global_id = [&](const Labels& ids) {
            auto found = combinations.lower_bound(ids);
            if (found != combinations.end() && found->first == ids) return found->second;
            Labels labels(cell_count);
            Integer score = 0;
            for (std::size_t c = 0; c < paths.size(); ++c) {
                const auto& members = units[c].vertices;
                const auto& local = paths[c].partitions[ids[c] - 1];
                score += paths[c].numerators[ids[c] - 1];
                for (std::size_t i = 0; i < members.size(); ++i) {
                    labels[members[i]] = members[local[i]];
                }
            }
            int id = next_structural_id(result.partitions.size());
            result.partitions.push_back(canonical_structural_labels(std::move(labels)));
            result.numerators.push_back(std::move(score));
            combinations.emplace_hint(found, ids, id);
            return id;
        };
        Labels state(paths.size());
        for (auto it = events.begin(); it != events.end(); ++it) {
            poll_path_interrupt();
            // At a coordinate, a closed singleton segment may be distinct
            // from both neighbouring open segments. Process the point first.
            for (const Change& c : it->second) if (c.point) state[c.unit] = c.id;
            const std::string start = it->first.str();
            append(result.segments, global_id(state), start, start, true, true);
            if (upper && it->first == *upper) break;
            for (const Change& c : it->second) if (c.right) state[c.unit] = c.id;
            auto next = std::next(it);
            const std::string end = next != events.end() ? next->first.str() :
                                    (upper ? upper->str() : "Inf");
            append(result.segments, global_id(state), start, end, false, false);
        }
        return result;
    }

public:
    // The caller lends its newly built graph for an ownership transfer. Map
    // nodes move into ordered subgraphs without allocating a second edge set.
    StructuralPlan(Network& input, const Integer& global_total)
        : total(global_total), cell_count(static_cast<int>(input.volume.size())) {
        Labels owner(cell_count, -1), local_index(cell_count);
        std::vector<Labels> members;
        Labels queue;
        int matching_unit = -1;
        for (int u = 0; u < cell_count; ++u) {
            if ((u & 1023) == 0) poll_path_interrupt();
            if (owner[u] >= 0) continue;
            const auto& adjacent = input.adjacency[u];
            const bool pair_or_isolate = adjacent.empty() ||
                (adjacent.size() == 1 && input.adjacency[adjacent.begin()->first].size() == 1);
            if (pair_or_isolate) {
                if (matching_unit < 0) {
                    matching_unit = static_cast<int>(members.size());
                    members.emplace_back();
                }
                owner[u] = matching_unit;
                if (!adjacent.empty()) owner[adjacent.begin()->first] = matching_unit;
                component_sizes.push_back(adjacent.empty() ? 1 : 2);
                continue;
            }
            const int id = static_cast<int>(members.size());
            members.emplace_back();
            queue.assign(1, u);
            owner[u] = id;
            for (std::size_t i = 0; i < queue.size(); ++i) {
                if ((i & 1023) == 0) poll_path_interrupt();
                for (const auto& item : input.adjacency[queue[i]]) {
                    int v = item.first;
                    if (owner[v] < 0) {
                        owner[v] = id;
                        queue.push_back(v);
                    }
                }
            }
            component_sizes.push_back(static_cast<int>(queue.size()));
        }
        std::size_t degree_sum = 0;
        for (int u = 0; u < cell_count; ++u) {
            auto& local = members[owner[u]];
            local_index[u] = static_cast<int>(local.size());
            local.push_back(u);
            degree_sum += input.adjacency[u].size();
        }
        edges = degree_sum / 2;
        for (std::size_t i = 0; i < members.size(); ++i) {
            units.emplace_back(std::move(members[i]), static_cast<int>(i) == matching_unit);
        }
        if (units.size() == 1) {
            units.front().graph = std::move(input);
        } else {
            for (auto& unit : units) unit.graph = Network(static_cast<int>(unit.vertices.size()));
            for (int u = 0; u < cell_count; ++u) {
                if ((u & 255) == 0) poll_path_interrupt();
                auto& local = units[owner[u]].graph;
                local.volume[local_index[u]] = std::move(input.volume[u]);
                auto& dest = local.adjacency[local_index[u]];
                auto& src = input.adjacency[u];
                while (!src.empty()) {
                    auto node = src.extract(src.begin());
                    node.key() = local_index[node.key()];
                    dest.insert(dest.end(), std::move(node));
                }
            }
            input = Network(0);
        }
        for (auto& unit : units) {
            unit.prepare(total);
            if (unit.tail > tail) tail = unit.tail;
        }
    }

    IntervalData scan(const Rational& lower, const std::optional<Rational>& upper,
                      bool include_upper) const {
        if (units.size() == 1) return units.front().scan(total, lower, upper, include_upper);
        std::vector<IntervalData> paths;
        paths.reserve(units.size());
        for (const auto& unit : units) {
            poll_path_interrupt();
            paths.push_back(unit.scan(total, lower, upper, include_upper));
        }
        return compose(paths, upper, include_upper);
    }

    Rcpp::List metadata() const {
        const char* mode = !edges ? "edgeless" : (units.size() == 1 && units.front().matching) ?
                           "matching" : component_sizes.size() > 1 ? "components" : "connected";
        return Rcpp::List::create(Rcpp::_["mode"] = mode,
                                  Rcpp::_["n_components"] = static_cast<int>(component_sizes.size()),
                                  Rcpp::_["component_sizes"] = component_sizes,
                                  Rcpp::_["n_edges"] = static_cast<double>(edges),
                                  Rcpp::_["singleton_tail_start"] = tail.str());
    }
};

#endif
