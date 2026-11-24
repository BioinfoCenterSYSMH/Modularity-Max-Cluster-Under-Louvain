#include <Rcpp.h>
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <cmath>
#include <map>
#include <numeric>
#include <optional>
#include <vector>

namespace {
using Integer = boost::multiprecision::cpp_int;
using Rational = boost::multiprecision::cpp_rational;
using Labels = std::vector<int>;
using Neighbours = std::map<int, Integer>;

// Cross-unit edges are stored twice. A unit's volume retains the contribution
// of edges internal to it, including after contraction.
struct Network {
    std::vector<Neighbours> adjacency;
    std::vector<Integer> volume;
    explicit Network(int n) : adjacency(n), volume(n) {}
    void add_edge(int u, int v, const Integer& weight) {
        adjacency[u][v] += weight;
        adjacency[v][u] += weight;
    }
};

struct Trace {
    Integer num, den;
    bool right;
    Integer next_num = 0, next_den = 0;
    Trace(const Rational& start, bool right_limit)
        : num(numerator(start)), den(denominator(start)), right(right_limit) {}

    // At an exact tie, the smaller penalty wins immediately to the right.
    int compare(const Integer& a, const Integer& b) const {
        Integer delta = a * den - b * num;
        if (delta != 0) return delta.sign();
        return right ? -b.sign() : 0;
    }

    // Only a challenger with a smaller penalty can overtake the winner.
    // Save unreduced fractions here. A gcd is needed only for the final bound.
    void constrain(const Integer& a, const Integer& b) {
        if (next_den == 0 || a * next_den < next_num * b) {
            next_num = a;
            next_den = b;
        }
    }

    std::optional<Rational> next() const {
        if (next_den == 0) return std::nullopt;
        return Rational(next_num, next_den);
    }
};

Labels move_units(const Network& g, const Integer& twice_weight, Trace& trace) {
    int n = static_cast<int>(g.volume.size());
    Labels group(n);
    std::iota(group.begin(), group.end(), 0);
    std::vector<Integer> volume = g.volume;
    std::vector<Integer> links(n);
    std::vector<bool> active(n, false);
    Labels targets;
    targets.reserve(n);
    bool changed;
    do {
        Rcpp::checkUserInterrupt();
        changed = false;
        for (int u = 0; u < n; ++u) {
            const int source = group[u];
            targets.clear();
            targets.push_back(source);
            active[source] = true;
            for (const auto& [v, w] : g.adjacency[u]) {
                int target = group[v];
                if (!active[target]) {
                    targets.push_back(target);
                    active[target] = true;
                }
                links[target] += w;
            }
            volume[source] -= g.volume[u];
            int best = source;
            for (int target : targets) {
                if (target == source) continue;
                Integer a = twice_weight * (links[target] - links[best]);
                Integer b = g.volume[u] * (volume[target] - volume[best]);
                int order = trace.compare(a, b);
                if (order > 0 || (order == 0 && best != source && target < best)) {
                    best = target;
                }
            }
            if (trace.right) {
                for (int target : targets) {
                    if (volume[best] > volume[target]) {
                        trace.constrain(twice_weight * (links[best] - links[target]),
                                        g.volume[u] * (volume[best] - volume[target]));
                    }
                }
            }
            for (int target : targets) {
                links[target] = 0;
                active[target] = false;
            }
            volume[best] += g.volume[u];
            group[u] = best;
            if (best != source) changed = true;
        }
    } while (changed);
    // Canonicalize in vertex order. Contracted units are therefore always
    // visited in increasing order of their smallest original cell index.
    Labels ids(n, -1);
    int count = 0;
    for (int& id : group) {
        if (ids[id] < 0) ids[id] = count++;
        id = ids[id];
    }
    return group;
}

Network contract(const Network& g, const Labels& group, int count) {
    Network coarse(count);
    for (int u = 0; u < static_cast<int>(group.size()); ++u) {
        coarse.volume[group[u]] += g.volume[u];
        for (const auto& [v, w] : g.adjacency[u]) {
            if (u < v && group[u] != group[v]) coarse.add_edge(group[u], group[v], w);
        }
    }
    return coarse;
}

Labels run(const Network& original, const Integer& twice_weight, Trace& trace) {
    Labels labels(original.volume.size());
    std::iota(labels.begin(), labels.end(), 0);
    const Network* current = &original;
    Network coarse(0);
    for (;;) {
        Labels group = move_units(*current, twice_weight, trace);
        int count = 1 + *std::max_element(group.begin(), group.end());
        for (int& label : labels) label = group[label];
        if (count == static_cast<int>(group.size())) return labels;
        coarse = contract(*current, group, count);
        current = &coarse;
    }
}

struct Segment {
    int id;
    std::string lower, upper;
    bool left_closed, right_closed;
};

void append(std::vector<Segment>& segments, int id, const std::string& lower,
            const std::string& upper, bool left_closed, bool right_closed) {
    if (!segments.empty() && segments.back().id == id) {
        segments.back().upper = upper;
        segments.back().right_closed = right_closed;
    } else {
        segments.push_back({id, lower, upper, left_closed, right_closed});
    }
}

// All partitions share the denominator (2W)^2, so their integer numerators
// determine both the maximum and exact ties, even for stored binary weights.
Integer classic_score(const Network& graph, const Labels& labels, const Integer& twice_weight) {
    std::vector<Integer> volume(graph.volume.size());
    Integer internal = 0;
    for (int u = 0; u < static_cast<int>(labels.size()); ++u) {
        volume[labels[u]] += graph.volume[u];
        for (const auto& [v, w] : graph.adjacency[u]) {
            if (u < v && labels[u] == labels[v]) internal += w;
        }
    }
    Integer score = 2 * twice_weight * internal;
    for (const Integer& v : volume) score -= v * v;
    return score;
}

Rcpp::DataFrame recommend(const std::vector<Segment>& segments,
                          const Rcpp::LogicalVector& is_best) {
    Rcpp::CharacterVector status(1, "undefined_modularity"), infimum(1, NA_STRING),
        minimum(1, NA_STRING), witness(1, NA_STRING);
    Rcpp::IntegerVector partition(1, NA_INTEGER), witness_partition(1, NA_INTEGER);
    Rcpp::NumericVector approximate(1, NA_REAL);
    for (const auto& s : segments) {
        if (is_best[s.id - 1] != TRUE) continue;
        Rational low(s.lower);
        Rational sample = low;
        if (s.left_closed) {
            status[0] = "minimum_attained";
            minimum[0] = s.lower;
            approximate[0] = low.convert_to<double>();
            partition[0] = s.id;
        } else {
            status[0] = "open_infimum";
            if (s.upper == "Inf") sample += 1;
            else sample = (low + Rational(s.upper)) / 2;
        }
        infimum[0] = s.lower;
        witness[0] = sample.str();
        witness_partition[0] = s.id;
        break;
    }
    return Rcpp::DataFrame::create(
        Rcpp::_["status"] = status, Rcpp::_["recommended_resolution"] = minimum,
        Rcpp::_["recommended_resolution_numeric"] = approximate,
        Rcpp::_["partition"] = partition, Rcpp::_["infimum"] = infimum,
        Rcpp::_["representative_resolution"] = witness,
        Rcpp::_["representative_partition"] = witness_partition);
}
} // namespace

// [[Rcpp::export]]
Rcpp::List enumerate_path_cpp(int n, Rcpp::IntegerVector i, Rcpp::IntegerVector j,
                             Rcpp::IntegerVector type, Rcpp::NumericVector values,
                             Rcpp::NumericVector overlap, int k) {
    std::vector<Rational> fractions;
    Integer scale = 1;
    for (R_xlen_t t = 0; t < values.size(); ++t) {
        Rational w;
        if (k) {
            Integer s = static_cast<int>(overlap[t]);
            w = Rational(s, Integer(2) * k - s);
        } else {
            // Exact binary rational of the stored finite double.
            w = Rational(static_cast<double>(values[t]));
        }
        fractions.push_back(w);
        scale = boost::multiprecision::lcm(scale, denominator(w));
    }
    std::vector<Integer> weights;
    for (const auto& w : fractions) weights.push_back(numerator(w) * (scale / denominator(w)));
    Network graph(n);
    Integer twice_weight = 0;
    for (R_xlen_t idx = 0; idx < i.size(); ++idx) {
        int u = i[idx] - 1, v = j[idx] - 1;
        const Integer& w = weights[type[idx] - 1];
        graph.add_edge(u, v, w);
        graph.volume[u] += w;
        graph.volume[v] += w;
        twice_weight += 2 * w;
    }

    std::map<Labels, int> ids;
    auto id_for = [&](const Labels& labels) {
        return ids.emplace(labels, static_cast<int>(ids.size()) + 1).first->second;
    };
    std::vector<Segment> segments;
    Rational start = 0;
    for (;;) {
        Rcpp::checkUserInterrupt();
        std::string lower = start.str();
        Trace point(start, false);
        append(segments, id_for(run(graph, twice_weight, point)), lower, lower, true, true);
        Trace after(start, true);
        int id = id_for(run(graph, twice_weight, after));
        auto next = after.next();
        append(segments, id, lower, next ? next->str() : "Inf", false, false);
        if (!next) break;
        start = *next;
    }
    Rcpp::IntegerMatrix membership(n, ids.size());
    std::vector<Integer> numerators(ids.size());
    for (const auto& [labels, id] : ids) {
        for (int u = 0; u < n; ++u) membership(u, id - 1) = labels[u] + 1;
        numerators[id - 1] = classic_score(graph, labels, twice_weight);
    }
    Rcpp::CharacterVector exact(ids.size(), NA_STRING);
    Rcpp::NumericVector modularity(ids.size(), NA_REAL);
    Rcpp::LogicalVector is_best(ids.size(), NA_LOGICAL);
    if (twice_weight > 0) {
        Integer denominator = twice_weight * twice_weight;
        Integer maximum = *std::max_element(numerators.begin(), numerators.end());
        for (std::size_t idx = 0; idx < numerators.size(); ++idx) {
            Rational q(numerators[idx], denominator);
            exact[idx] = q.str();
            modularity[idx] = q.convert_to<double>();
            is_best[idx] = numerators[idx] == maximum;
        }
    }
    Rcpp::IntegerVector partition(segments.size());
    Rcpp::CharacterVector lower(segments.size()), upper(segments.size());
    Rcpp::LogicalVector left_closed(segments.size()), right_closed(segments.size());
    for (std::size_t row = 0; row < segments.size(); ++row) {
        const auto& s = segments[row];
        partition[row] = s.id;
        lower[row] = s.lower;
        upper[row] = s.upper;
        left_closed[row] = s.left_closed;
        right_closed[row] = s.right_closed;
    }
    return Rcpp::List::create(
        Rcpp::_["membership"] = membership,
        Rcpp::_["scores"] = Rcpp::DataFrame::create(
            Rcpp::_["modularity"] = modularity, Rcpp::_["modularity_exact"] = exact,
            Rcpp::_["is_max"] = is_best),
        Rcpp::_["recommendation"] = recommend(segments, is_best),
        Rcpp::_["intervals"] = Rcpp::DataFrame::create(
            Rcpp::_["partition"] = partition, Rcpp::_["lower"] = lower,
            Rcpp::_["upper"] = upper, Rcpp::_["lower_closed"] = left_closed,
            Rcpp::_["upper_closed"] = right_closed));
}
