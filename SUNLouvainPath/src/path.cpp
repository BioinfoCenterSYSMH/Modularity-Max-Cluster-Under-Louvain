#include <Rcpp.h>
#include "interval_threads.h"
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <cmath>
#include <map>
#include <numeric>
#include <optional>
#include <limits>
#include <set>
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
        poll_path_interrupt();
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

// Decimal user inputs are base ten, including values with leading zeroes.
// Boost's integer string constructor otherwise treats leading zeroes as octal.
Integer decimal_integer(const std::string& digits) {
    if (digits.empty() || digits.find_first_not_of("0123456789") != std::string::npos) {
        Rcpp::stop("Resolutions must be nonnegative numbers or integer fractions.");
    }
    auto begin = digits.find_first_not_of('0');
    return begin == std::string::npos ? Integer(0) : Integer(digits.substr(begin));
}

Rational resolution(const std::string& input) {
    bool negative = !input.empty() && input[0] == '-';
    std::string text = input.substr(!input.empty() && (input[0] == '+' || negative) ? 1 : 0);
    std::size_t slash = text.find('/');
    if (slash != std::string::npos) {
        Integer num = decimal_integer(text.substr(0, slash));
        Integer den = decimal_integer(text.substr(slash + 1));
        if (negative && num != 0) Rcpp::stop("Resolutions cannot be negative.");
        if (den == 0) Rcpp::stop("A resolution fraction must have a positive denominator.");
        return Rational(num, den);
    }

    // Expanding a short exponent such as 1e999999999 into an integer would
    // otherwise allocate hundreds of MB before the input could be validated.
    long long exponent = 0;
    std::size_t e = text.find_first_of("eE");
    if (e != std::string::npos) {
        std::string suffix = text.substr(e + 1);
        text.resize(e);
        bool down = !suffix.empty() && suffix[0] == '-';
        if (down || (!suffix.empty() && suffix[0] == '+')) suffix.erase(0, 1);
        auto digits = decimal_integer(suffix);
        if (digits > 10000) Rcpp::stop("Scientific-notation exponents must be between -10000 and 10000.");
        exponent = digits.convert_to<int>();
        if (down) exponent = -exponent;
    }
    std::size_t dot = text.find('.');
    if (dot != std::string::npos) {
        exponent -= static_cast<long long>(text.size() - dot - 1);
        text.erase(dot, 1);
    }
    Integer mantissa = decimal_integer(text);
    if (mantissa == 0) return Rational(0);
    if (negative) Rcpp::stop("Resolutions cannot be negative.");
    auto magnitude = static_cast<unsigned long long>(std::abs(exponent));
    if (magnitude > std::numeric_limits<unsigned>::max()) Rcpp::stop("Decimal exponent is too large.");
    Integer power = boost::multiprecision::pow(Integer(10), static_cast<unsigned>(magnitude));
    if (exponent >= 0) return Rational(mantissa * power);
    return Rational(mantissa, power);
}

std::optional<Rational> upper_limit(const std::string& text) {
    if (text == "Inf") return std::nullopt;
    return resolution(text);
}

std::vector<Rational> interior_splits(Rcpp::CharacterVector points,
                                      const std::optional<Rational>& limit) {
    std::set<Rational> interior;
    for (R_xlen_t i = 0; i < points.size(); ++i) {
        if (Rcpp::CharacterVector::is_na(points[i])) Rcpp::stop("Split points cannot be missing.");
        Rational value = resolution(Rcpp::as<std::string>(points[i]));
        if (value > 0 && (!limit || value < *limit)) interior.insert(std::move(value));
    }
    return {interior.begin(), interior.end()};
}

Network build_graph(int n, Rcpp::IntegerVector i, Rcpp::IntegerVector j, Rcpp::IntegerVector type,
                    Rcpp::NumericVector values, Rcpp::NumericVector overlap, int k, Integer& total) {
    std::vector<Rational> fractions;
    Integer scale = 1;
    for (R_xlen_t t = 0; t < values.size(); ++t) {
        Rational w;
        if (k) {
            Integer s = static_cast<int>(overlap[t]);
            w = Rational(s, Integer(2) * k - s);
        } else {
            w = Rational(static_cast<double>(values[t]));
        }
        fractions.push_back(w);
        scale = boost::multiprecision::lcm(scale, denominator(w));
    }
    std::vector<Integer> weights;
    for (const auto& w : fractions) weights.push_back(numerator(w) * (scale / denominator(w)));
    Network graph(n);
    for (R_xlen_t idx = 0; idx < i.size(); ++idx) {
        int u = i[idx] - 1, v = j[idx] - 1;
        const Integer& w = weights[type[idx] - 1];
        graph.add_edge(u, v, w);
        graph.volume[u] += w;
        graph.volume[v] += w;
        total += 2 * w;
    }
    return graph;
}

using PartitionIndex = std::map<Labels, int>;

std::vector<Labels> take_partitions(PartitionIndex& index) {
    std::vector<Labels> out(index.size());
    while (!index.empty()) {
        auto node = index.extract(index.begin());
        out[node.mapped() - 1] = std::move(node.key());
    }
    return out;
}

struct IntervalData {
    std::vector<Labels> partitions;
    std::vector<Integer> numerators;
    std::vector<Segment> segments;
};

IntervalData scan_interval(const Network& graph, const Integer& total, Rational start,
                           const std::optional<Rational>& limit, bool include_upper) {
    PartitionIndex ids;
    auto id_for = [&](Labels labels) {
        return ids.try_emplace(std::move(labels), static_cast<int>(ids.size()) + 1).first->second;
    };
    IntervalData block;
    for (;;) {
        poll_path_interrupt();
        const std::string here = start.str();
        Trace point(start, false);
        append(block.segments, id_for(run(graph, total, point)), here, here, true, true);
        if (limit && start == *limit) break;
        Trace after(start, true);
        int id = id_for(run(graph, total, after));
        auto next = after.next();
        // A right trace certifies the open interval up to the next crossing or the cut.
        if (limit && (!next || *next >= *limit)) {
            append(block.segments, id, here, limit->str(), false, false);
            if (!include_upper) break;
            start = *limit;
            continue;
        }
        append(block.segments, id, here, next ? next->str() : "Inf", false, false);
        if (!next) break;
        start = *next;
    }
    block.partitions = take_partitions(ids);
    block.numerators.reserve(block.partitions.size());
    for (const auto& labels : block.partitions) {
        poll_path_interrupt();
        block.numerators.push_back(classic_score(graph, labels, total));
    }
    return block;
}

IntervalData merge_intervals(std::vector<IntervalData> blocks) {
    if (blocks.size() == 1) return std::move(blocks.front());
    IntervalData result;
    PartitionIndex index;
    for (auto& block : blocks) {
        std::vector<int> ids;
        ids.reserve(block.partitions.size());
        // Each block and its partitions arrive in ascending first-appearance order,
        // regardless of the order in which individual workers completed.
        for (std::size_t i = 0; i < block.partitions.size(); ++i) {
            auto entry = index.try_emplace(std::move(block.partitions[i]), static_cast<int>(index.size()) + 1);
            ids.push_back(entry.first->second);
            if (entry.second) result.numerators.push_back(std::move(block.numerators[i]));
        }
        for (const auto& s : block.segments) {
            append(result.segments, ids[s.id - 1], s.lower, s.upper, s.left_closed, s.right_closed);
        }
        block = IntervalData{};
    }
    result.partitions = take_partitions(index);
    return result;
}

Rcpp::List to_r(const IntervalData& path, const Integer& total) {
    const std::size_t count = path.partitions.size();
    Rcpp::IntegerMatrix membership(path.partitions.front().size(), count);
    for (std::size_t idx = 0; idx < count; ++idx) {
        Rcpp::checkUserInterrupt();
        const auto& labels = path.partitions[idx];
        for (std::size_t u = 0; u < labels.size(); ++u) membership(u, idx) = labels[u] + 1;
    }
    Rcpp::CharacterVector exact(count, NA_STRING);
    Rcpp::NumericVector modularity(count, NA_REAL);
    Rcpp::LogicalVector is_best(count, NA_LOGICAL);
    if (total > 0) {
        Integer den = total * total;
        Integer maximum = *std::max_element(path.numerators.begin(), path.numerators.end());
        for (std::size_t idx = 0; idx < count; ++idx) {
            Rational q(path.numerators[idx], den);
            exact[idx] = q.str();
            modularity[idx] = q.convert_to<double>();
            is_best[idx] = path.numerators[idx] == maximum;
        }
    }
    const auto& segments = path.segments;
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
} // namespace

// [[Rcpp::export(rng = false)]]
Rcpp::List resolution_ranges_cpp(Rcpp::CharacterVector split_points, std::string r_max) {
    auto limit = upper_limit(r_max);
    auto splits = interior_splits(split_points, limit);
    Rcpp::CharacterVector points(splits.size());
    for (std::size_t i = 0; i < splits.size(); ++i) points[i] = splits[i].str();
    return Rcpp::List::create(Rcpp::_["split_points"] = points,
                              Rcpp::_["r_max"] = limit ? limit->str() : std::string("Inf"));
}

// [[Rcpp::export(rng = false)]]
Rcpp::List enumerate_interval_cpp(int n, Rcpp::IntegerVector i, Rcpp::IntegerVector j,
                                  Rcpp::IntegerVector type, Rcpp::NumericVector values,
                                  Rcpp::NumericVector overlap, int k, std::string lower,
                                  std::string upper, bool include_upper) {
    auto limit = upper_limit(upper);
    auto start = resolution(lower);
    if (limit && (*limit < start || (*limit == start && !include_upper))) {
        Rcpp::stop("The resolution interval must be nonempty.");
    }
    Integer total = 0;
    auto graph = build_graph(n, i, j, type, values, overlap, k, total);
    return to_r(scan_interval(graph, total, start, limit, include_upper), total);
}

// [[Rcpp::export(rng = false)]]
Rcpp::List enumerate_parallel_cpp(int n, Rcpp::IntegerVector i, Rcpp::IntegerVector j,
                                  Rcpp::IntegerVector type, Rcpp::NumericVector values,
                                  Rcpp::NumericVector overlap, int k, Rcpp::CharacterVector split_points,
                                  std::string r_max, int workers) {
    auto limit = upper_limit(r_max);
    auto starts = interior_splits(split_points, limit);
    starts.insert(starts.begin(), Rational(0));
    if (workers < 1) Rcpp::stop("workers must be a positive integer.");
    Integer total = 0;
    auto graph = build_graph(n, i, j, type, values, overlap, k, total);
    auto blocks = map_intervals(starts.size(), workers, [&](std::size_t idx) {
        bool last = idx + 1 == starts.size();
        auto end = last ? limit : std::optional<Rational>(starts[idx + 1]);
        return scan_interval(graph, total, starts[idx], end, last && limit.has_value());
    });
    return to_r(merge_intervals(std::move(blocks)), total);
}

// [[Rcpp::export(rng = false)]]
Rcpp::List enumerate_path_cpp(int n, Rcpp::IntegerVector i, Rcpp::IntegerVector j,
                              Rcpp::IntegerVector type, Rcpp::NumericVector values,
                              Rcpp::NumericVector overlap, int k) {
    return enumerate_interval_cpp(n, i, j, type, values, overlap, k, "0", "Inf", false);
}
