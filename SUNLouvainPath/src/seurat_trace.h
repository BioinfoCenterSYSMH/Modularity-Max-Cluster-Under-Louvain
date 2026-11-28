#ifndef MML_SEURAT_TRACE_H
#define MML_SEURAT_TRACE_H

#include <boost/multiprecision/cpp_int.hpp>
#include <optional>

namespace mml_s55 {
using Integer = boost::multiprecision::cpp_int;
using Rational = boost::multiprecision::cpp_rational;

struct Edge {
    int u, v;
    Integer w;
};

// A right-limit trace fixes every comparison of a+b*r until the first
// subsequent root on that execution. This includes comparisons between
// the final quality functions of different random starts. Exact-point
// traces use the optimizer's own tie rules.
struct Trace {
    const bool right;
    bool differs_at_start = false;

    explicit Trace(const Rational& start, bool right_limit)
        : right(right_limit), num(numerator(start)), den(denominator(start)) {}

    int compare(const Integer& a, const Integer& b) {
        if (b == 0) return a.sign();
        const Integer value = a * den + b * num;
        const int sign = value.sign();
        if (!right) return sign;
        if (sign == 0) {
            differs_at_start = true;
            return b.sign();
        }
        if (sign != b.sign()) {
            // This root is strictly after the current nonnegative start.
            // Compare fractions by cross multiplication, reducing only the
            // winning boundary once, after the optimizer has returned.
            const Integer candidate_num = sign > 0 ? a : -a;
            const Integer candidate_den = sign > 0 ? -b : b;
            if (end_den == 0 || candidate_num * end_den < end_num * candidate_den) {
                end_num = candidate_num;
                end_den = candidate_den;
            }
        }
        return sign;
    }

    std::optional<Rational> next() const {
        if (end_den == 0) return std::nullopt;
        return Rational(end_num, end_den);
    }

private:
    Integer num, den, end_num = 0, end_den = 0;
};
} // namespace mml_s55

#endif
