#ifndef SUNLOUVAINPATH_CLUSTER_CAP_H
#define SUNLOUVAINPATH_CLUSTER_CAP_H

// Included in path.cpp's anonymous namespace. For c <= K clusters, the
// within-cluster off-diagonal null mass is at least b = 1/K - sum(d_i/D)^2,
// where D = sum_i d_i. Strict improvement over singletons requires the
// observed mass divided by the null mass to exceed r. An upper bound on
// that ratio is the average of the best b units of null mass over all
// unordered pairs, ranked by D*w_ij/(d_i*d_j). Nonedges have ratio zero.
std::optional<Rational> edge_cluster_bound(const Network& graph, const Integer& total,
                                          int max_clusters) {
    if (max_clusters == 0 || static_cast<std::size_t>(max_clusters) >= graph.volume.size() ||
        total == 0) return std::nullopt;
    Integer sum_squares = 0;
    for (const Integer& degree : graph.volume) sum_squares += degree * degree;
    const Integer square = total * total;
    const Integer budget = square - max_clusters * sum_squares;
    if (budget <= 0) return std::nullopt;

    struct Edge {
        const Integer* weight;
        Integer degree_product;
    };
    std::vector<Edge> edges;
    std::size_t directed_edges = 0;
    for (const auto& neighbours : graph.adjacency) directed_edges += neighbours.size();
    edges.reserve(directed_edges / 2);
    for (int u = 0; u < static_cast<int>(graph.volume.size()); ++u) {
        if ((u & 511) == 0) poll_path_interrupt();
        for (const auto& [v, w] : graph.adjacency[u]) {
            if (u < v) edges.push_back({&w, graph.volume[u] * graph.volume[v]});
        }
    }
    std::size_t comparisons = 0;
    std::sort(edges.begin(), edges.end(), [&](const Edge& x, const Edge& y) {
        if ((++comparisons & 65535) == 0) poll_path_interrupt();
        return *x.weight * y.degree_product > *y.weight * x.degree_product;
    });

    // In units of d_i*d_j, exactly budget/(2*K) mass can be filled. The
    // last edge can be used fractionally; ties have identical density.
    const Integer twice_k = 2 * Integer(max_clusters);
    const Integer quota_ceiling = (budget + twice_k - 1) / twice_k;
    Integer weight_used = 0, mass_used = 0;
    std::size_t index = 0;
    for (const Edge& edge : edges) {
        if ((index++ & 16383) == 0) poll_path_interrupt();
        if (mass_used + edge.degree_product >= quota_ceiling) {
            const Integer mixed = twice_k * weight_used * edge.degree_product +
                (budget - twice_k * mass_used) * *edge.weight;
            return Rational(total * mixed, budget * edge.degree_product);
        }
        mass_used += edge.degree_product;
        weight_used += *edge.weight;
    }
    return Rational(max_clusters * square, budget);
}

// The structural scanner has to examine all crossings before the certified
// cutoff, including traces that temporarily exceed K. Discard their results
// only when the full block is available, then merge eligible blocks.
IntervalData eligible_partitions(IntervalData block, int max_clusters) {
    if (max_clusters == 0) return block;
    IntervalData kept;
    std::vector<int> ids(block.partitions.size(), 0);
    for (std::size_t i = 0; i < block.partitions.size(); ++i) {
        poll_path_interrupt();
        auto& labels = block.partitions[i];
        // Canonical labels are contiguous, zero-based and cover every cell.
        if (std::any_of(labels.begin(), labels.end(),
                        [max_clusters](int group) { return group >= max_clusters; })) continue;
        ids[i] = next_structural_id(kept.partitions.size());
        kept.partitions.push_back(std::move(labels));
        kept.numerators.push_back(std::move(block.numerators[i]));
    }
    for (auto& s : block.segments) {
        s.id = ids[s.id - 1];
        if (s.id != 0) kept.segments.push_back(std::move(s));
    }
    return kept;
}
#endif
