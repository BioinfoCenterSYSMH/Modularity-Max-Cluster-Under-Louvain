#ifndef MML_PATH_COMMON_H
#define MML_PATH_COMMON_H

#include <Rcpp.h>
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <cmath>
#include <limits>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace mml_path_common {
using Integer = boost::multiprecision::cpp_int;
using Rational = boost::multiprecision::cpp_rational;
using Labels = std::vector<int>;

struct Segment {
    int id;
    std::string lower, upper;
    bool left_closed, right_closed;
};

inline void append(std::vector<Segment>& segments, int id, const std::string& lower,
            const std::string& upper, bool left_closed, bool right_closed) {
    // Capped output can have a missing point or a full gap between two
    // occurrences of the same partition. Merge only connected intervals.
    if (!segments.empty() && segments.back().id == id && segments.back().upper == lower &&
        (segments.back().right_closed || left_closed)) {
        segments.back().upper = upper;
        segments.back().right_closed = right_closed;
    } else {
        segments.push_back({id, lower, upper, left_closed, right_closed});
    }
}

// Decimal user inputs are base ten, including values with leading zeroes.
// Boost's integer string constructor otherwise treats leading zeroes as octal.
inline Integer decimal_integer(const std::string& digits) {
    if (digits.empty() || digits.find_first_not_of("0123456789") != std::string::npos) {
        Rcpp::stop("Resolutions must be nonnegative numbers or integer fractions.");
    }
    auto begin = digits.find_first_not_of('0');
    return begin == std::string::npos ? Integer(0) : Integer(digits.substr(begin));
}

inline Rational resolution(const std::string& input) {
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

inline std::optional<Rational> upper_limit(const std::string& text) {
    if (text == "Inf") return std::nullopt;
    return resolution(text);
}

inline std::vector<Rational> interior_splits(Rcpp::CharacterVector points,
                                      const std::optional<Rational>& limit) {
    std::set<Rational> interior;
    for (R_xlen_t i = 0; i < points.size(); ++i) {
        if (Rcpp::CharacterVector::is_na(points[i])) Rcpp::stop("Split points cannot be missing.");
        Rational value = resolution(Rcpp::as<std::string>(points[i]));
        if (value > 0 && (!limit || value < *limit)) interior.insert(std::move(value));
    }
    return {interior.begin(), interior.end()};
}

struct WeightEncoding {
    std::vector<Integer> weights;
    Integer scale;
};

inline WeightEncoding encode_weights(Rcpp::NumericVector values, Rcpp::NumericVector overlap, int k) {
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
    return {std::move(weights), std::move(scale)};
}

using PartitionIndex = std::map<Labels, int>;

inline std::vector<Labels> take_partitions(PartitionIndex& index) {
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

inline IntervalData merge_intervals(std::vector<IntervalData> blocks) {
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
            if (entry.second && !block.numerators.empty()) {
                result.numerators.push_back(std::move(block.numerators[i]));
            }
        }
        for (const auto& s : block.segments) {
            append(result.segments, ids[s.id - 1], s.lower, s.upper, s.left_closed, s.right_closed);
        }
        block = IntervalData{};
    }
    result.partitions = take_partitions(index);
    return result;
}

inline Rcpp::DataFrame interval_frame(const std::vector<Segment>& segments) {
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
    return Rcpp::DataFrame::create(
            Rcpp::_["partition"] = partition, Rcpp::_["lower"] = lower,
            Rcpp::_["upper"] = upper, Rcpp::_["lower_closed"] = left_closed,
            Rcpp::_["upper_closed"] = right_closed);
}
} // namespace mml_path_common

#endif
