// FindClusters 5.5 sequential GroupSingletons semantics. Membership used to
// compute a recipient group's size and connectivity includes earlier assignments.
Labels grouped_seurat_labels(Labels labels, const Network& graph, bool group_singletons,
                             Rcpp::Function& sample_tie, std::map<int, int>& tie_cache) {
    const int n = static_cast<int>(labels.size());
    std::vector<int> sizes(n);
    for (int group : labels) ++sizes[group];
    Labels recipients, singletons;
    std::vector<bool> seen(n);
    for (int u = 0; u < n; ++u) {
        int g = labels[u];
        if (sizes[g] == 1) singletons.push_back(u);
        else if (!seen[g]) { recipients.push_back(g); seen[g] = true; }
    }
    if (!group_singletons) {
        for (int u : singletons) labels[u] = n; // Native character label "singleton".
        return labels;
    }
    if (recipients.empty()) return labels; // Define the all-singleton boundary.
    for (int u : singletons) {
        poll_path_interrupt();
        std::vector<Integer> strength(n);
        for (const auto& [v, w] : graph.adjacency[u]) strength[labels[v]] += w;
        Labels best;
        for (int g : recipients) {
            if (best.empty()) { best.push_back(g); continue; }
            int lead = best.front();
            Integer delta = strength[g] * sizes[lead] - strength[lead] * sizes[g];
            if (delta > 0) best.clear();
            if (delta >= 0) best.push_back(g);
        }
        int chosen = best.front();
        if (best.size() > 1) {
            int count = static_cast<int>(best.size());
            auto it = tie_cache.find(count);
            if (it == tie_cache.end()) {
                int offset = Rcpp::as<int>(sample_tie(count)) - 1;
                it = tie_cache.emplace(count, offset).first;
            }
            chosen = best[it->second];
        }
        labels[u] = chosen;
        ++sizes[chosen];
    }
    return labels;
}

struct SeuratQueries {
    Rcpp::IntegerVector raw, final;
    Rcpp::CharacterVector text, status;
    Rcpp::IntegerMatrix idents;
    std::map<int, std::vector<int>> columns;
    SeuratQueries(Rcpp::CharacterVector input, const Rcpp::DataFrame& intervals,
                  int n, const std::optional<Rational>& requested, int fxn)
        : raw(input.size(), NA_INTEGER), final(input.size(), NA_INTEGER),
          text(input.size()), status(input.size()), idents(n, input.size()) {
        std::fill(idents.begin(), idents.end(), NA_INTEGER);
        std::map<Rational, std::vector<int>> pending;
        for (R_xlen_t q = 0; q < input.size(); ++q) {
            Rational point = resolution(Rcpp::as<std::string>(input[q]));
            text[q] = point.str();
            if (fxn == 2 && point > 1) status[q] = "outside_modularity_domain";
            else if (requested && point > *requested) status[q] = "outside_r_max";
            else pending[point].push_back(q);
        }
        Rcpp::IntegerVector ids = intervals["partition"];
        Rcpp::CharacterVector upper = intervals["upper"];
        Rcpp::LogicalVector closed = intervals["upper_closed"];
        for (R_xlen_t s = 0; s < ids.size() && !pending.empty(); ++s) {
            auto end = upper_limit(Rcpp::as<std::string>(upper[s]));
            while (!pending.empty()) {
                auto it = pending.begin();
                if (end && (it->first > *end || (it->first == *end && !closed[s]))) break;
                for (int q : it->second) {
                    raw[q] = ids[s];
                    columns[ids[s]].push_back(q);
                }
                pending.erase(it);
            }
        }
        if (!pending.empty()) Rcpp::stop("Incomplete optimizer path for the requested resolutions.");
    }
};
