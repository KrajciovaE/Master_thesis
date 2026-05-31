#include <iostream>
#include <vector>
#include <sstream>
#include <algorithm>
#include <chrono>
#include <deque>
#include <queue>
#include <cstdint>
#include <bit>

#include <fstream>
#include <filesystem>


using namespace std;
using namespace std::chrono;
namespace fs = std::filesystem;


class Graph {
public:
    int V;
    vector<vector<int>> adj;

    explicit Graph(int V) : V(V) {
        this->V = V;
        adj.resize(V);
    }

    void addEdge(int u, int v) {
        if (find(adj[u].begin(), adj[u].end(), v) == adj[u].end()) {
            adj[u].push_back(v);
        }
        if (find(adj[v].begin(), adj[v].end(), u) == adj[v].end()) {
            adj[v].push_back(u);
        }
    }

    // Return the common degree (assuming the graph is regular).
    int degree() const {
        if (V == 0) return 0;
        return static_cast<int>(adj[0].size());
    }

    // Check if the graph is regular (all vertices have the same degree).
    bool isRegular() const {
        if (V == 0) return true;
        int d = static_cast<int>(adj[0].size());
        for (int i = 1; i < V; ++i) {
            if (static_cast<int>(adj[i].size()) != d) {
                return false;
            }
        }
        return true;
    }

    void inputGraph() {
        // Reads an adjacency list from standard input.
        // Each of the next V lines corresponds to one vertex i (0-based index)
        // and contains all its neighbours separated by spaces.
        //
        // Example for a 3-regular graph on 4 vertices:
        // 1 2 3
        // 0 2 3
        // 0 1 3
        // 0 1 2
        for (int i = 0; i < V; ++i) {
            string line;
            // Skip empty lines if any
            do {
                if (!getline(cin, line)) {
                    break;
                }
            } while (line.empty());

            if (line.empty()) continue;

            stringstream ss(line);
            int neighbor;
            while (ss >> neighbor) {
                addEdge(i, neighbor);
            }
        }
    }
};

// Global best cycle storage
static vector<int> bestCycle;
static int maxCycleLen = 0;
static bool foundMaxBound = false;

// Global banned mask to avoid duplicate cycle searches (used in cubic version)
static uint64_t bannedMask = 0ULL;

// Helper functions to work with bit masks (for cubic-specific algorithm)
inline bool isSet(uint64_t mask, int v) {
    return (mask & (1ULL << v)) != 0ULL;
}
inline void setBit(uint64_t &mask, int v) {
    mask |= (1ULL << v);
}
inline void clearBit(uint64_t &mask, int v) {
    mask &= ~(1ULL << v);
}

// Portable popcount for 64-bit masks
inline int popcount64(uint64_t x) {
#if defined(__GNUG__) || defined(__clang__)
    return __builtin_popcountll(x);
#else
    return static_cast<int>(std::popcount(x));
#endif
}

void printIgnoredMask(uint64_t mask, int V, const std::string& label = "ignored") {
    cout << "[" << label << "] ";
    bool first = true;
    for (int v = 0; v < V; ++v) {
        if (mask & (1ULL << v)) {
            if (!first) cout << ", ";
            cout << v;
            first = false;
        }
    }
    if (first) cout << "(empty)";
    cout << "\n";
}

// Forward declaration of the cubic-specific DFS
void dfsInducedCycleMaskGeneral(const Graph &g, int current, int parent,
                         deque<int> &path,
                         uint64_t visitedMask, uint64_t ignoredMask,
                         int cutoff);

// This function applies forced back-additions and returns true when cycle is detected.
bool applyForcedAdditions(const Graph &g,
                          deque<int> &path,
                          uint64_t &visitedMask,
                          uint64_t &ignoredMask)
{
    bool changed = true;
    while (changed) {
        changed = false;

        /// DEBUG
//        cout << "[applyForcedAdditions] Current path: ";
//        for (auto v : path) cout << v << " ";
//        cout << "\n";

        if (path.empty()) return false;

        int frontV = path.front();
        int secondFromFront = -1;
        if (path.size() >= 2) {
            secondFromFront = path[1];
        }

        // Check forced additions at the front of the path.
        {
            int neighborsWithNewVertex = 0;
            int candidate = -1;

            for (int nb : g.adj[frontV]) {
                if (nb == secondFromFront) continue; // Do not go back immediately.

                if (isSet(visitedMask, nb)) {
                    // Already visited neighbour.
                    if (nb == path.back() && path.size() >= 3) {
                        // cycle found
                        int cycleLen = static_cast<int>(path.size());
                        if (cycleLen > maxCycleLen) {
                            maxCycleLen = cycleLen;
                            bestCycle.assign(path.begin(), path.end());
                        }
                        /// DEBUG
//                        cout << "[applyForcedAdditions] CFound cycle: ";
//                        for (auto v : path) cout << v << " ";
//                        cout << "\n";
                        return true;
                    } else {
                        // chord -> path cannot be extended in an induced way
                        /// DEBUG:
                        //cout << "[applyForcedAdditions] Potential chord/cycle at front between " << frontV << " and " << nb << endl;
                        ignoredMask |= (1ULL << frontV);
                        return false;
                    }
                } else if (!isSet(ignoredMask, nb)) {
                    neighborsWithNewVertex++;
                    candidate = nb;
                }
            }

            if (neighborsWithNewVertex == 0) {
                ignoredMask |= (1ULL << frontV);
                return false;
            }

            if (neighborsWithNewVertex > 1) {
                // No forced addition.
            } else if (neighborsWithNewVertex == 1) {
                // Forced extension at the front.
                int forced = candidate;
                path.push_front(forced);

                /// DEBUG:
                //cout << "[applyForcedAdditions] Forcing neighbor " << forced << " in front of path\n";

                setBit(visitedMask, forced);
                changed = true;
                continue;
            }
        }
    }
    return false;
}

// The helper ignores one neighbour while adding other one to front and back of the path for the first vertex.
void firstExtension(const Graph &g,
                    int a, int b,   // neighbors to add
                    int start,
                    deque<int> &path,
                    uint64_t visitedMask,
                    uint64_t ignoredMask,
                    int cutoff)
{

    path.push_back(a);
    setBit(visitedMask, a);
    path.push_front(b);
    setBit(visitedMask, b);

    for(int nb : g.adj[start]) {
        if (nb != a && nb != b) setBit(ignoredMask, nb);
    }

    /// DEBUG
//    cout << "[firstExtension] Current path: ";
//    for (auto v : path) cout << v << " ";
//    cout << "\n";

    int current = path.back();
    int parent = start;
    dfsInducedCycleMaskGeneral(g, current, parent, path, visitedMask, ignoredMask, cutoff);
}

// DFS for induced cycles in a general d-regular graph.
// Path can be extended at the back in this function;
// forced additions may extend at the front via applyForcedAdditions.
void dfsInducedCycleMaskGeneral(const Graph &g, int current, int parent,
                                deque<int> &path,
                                uint64_t visitedMask, uint64_t ignoredMask,
                                int cutoff)
{
    // Dynamic pruning: if even adding all remaining non-banned vertices
    // cannot exceed current best, backtrack.
    int remainingVertices = g.V - popcount64(visitedMask | bannedMask);
    if (static_cast<int>(path.size()) + remainingVertices <= maxCycleLen) {
        return;
    }

    // If the path is too short, we haven't "chosen a direction" yet.
    // We systematically try all unordered pairs of neighbours of the start vertex.
    if (path.size() < 3) {
        if (path.empty()) return;

        int startV = path.front();
        const auto &nbrs = g.adj[startV];
        int deg = static_cast<int>(nbrs.size());

        // For each unordered pair (a, b) of neighbours of startV,
        // we start a new branch via firstExtension.
        for (int i = 0; i < deg; ++i) {
            for (int j = i + 1; j < deg; ++j) {
                int a = nbrs[i];
                int b = nbrs[j];

                // Optionally respect bannedMask for neighbours as well:
                // if either neighbour is globally banned, skip this pair.
                if (isSet(bannedMask, a) || isSet(bannedMask, b)) {
                    continue;
                }

                // Local copies so that each pair exploration starts from
                // the same initial path and masks.
                uint64_t locVisited = visitedMask;
                uint64_t locIgnored = ignoredMask;
                deque<int> localPath = path; // currently [startV]

                firstExtension(g, a, b, startV,
                               localPath, locVisited, locIgnored, cutoff);

                if (foundMaxBound) return;
            }
        }

        // After exploring all pairs from this start, nothing more to do in this call.
        return;
    }
    else {
        // Try extending the path from 'current'
        for (int nb : g.adj[current]) {
            // Don't go directly back to parent
            if (nb == parent) continue;

//            cout << "[dfsInducedCycleMask] current: " << current << " looking at nb: " << nb << endl;
//            cout << "[dfsInducedCycleMask] current ignored list: ";
//            printIgnoredMask(ignoredMask,g.V);

            // Respect global banned vertices and local ignored vertices
            if (isSet(bannedMask, nb) || isSet(ignoredMask, nb)) {
                //cout << "[dfsInducedCycleMask] nb is banned or ignored" << endl;
                continue;
            }

            // Cycle closure: edge from current to current start (path.front()).
            if (nb == path.front() && path.size() >= 3) {
                int cycleLen = static_cast<int>(path.size());
                if (cycleLen > maxCycleLen) {
                    maxCycleLen = cycleLen;
                    bestCycle.assign(path.begin(), path.end());
                    /// DEBUG:
//                    cout << "[dfsInducedCycleMask] Found longest cycle yet: ";
//                    for (auto v: path) cout << v << " ";
//                    cout << "\n";
                }
                if (maxCycleLen >= cutoff) {
                    foundMaxBound = true;
                }
                /// DEBUG:
//                cout << "[dfsInducedCycleMask] Found a cycle of len "
//                     << cycleLen << " closing at " << path.front() << "\n";
                return;
            }

            // Never revisit vertices already on the path
            if (isSet(visitedMask, nb)) {
                continue;
            }

            // nb must see exactly ONE visited vertex (the current endpoint)
            int neighboursInVisited = 0;
            for (int w: g.adj[nb]) {
                if (isSet(visitedMask, w) && w != path.front()) {
                    neighboursInVisited++;
                }
            }
            /// DEBUG:
//            cout << "[dfsInducedCycleMask] current=" << current
//                 << ", path.size()=" << path.size()
//                 << ", neighbors count= " << neighboursInVisited << "\n";

            if (neighboursInVisited != 1) {
                // This vertex would break the induced property (chord or disconnected),
                // so remember it in ignoredMask and never try it again from this branch.
                setBit(ignoredMask, nb);
                /// DEBUG:
                //cout << "[dfsInducedCycleMask] adding " << nb << " to ignored" << endl;
                continue;
            }

            // Optional heuristic: try forced additions from here.
            bool found = false;
            int front = path.front();
//            printIgnoredMask(ignoredMask,g.V);
            if (applyForcedAdditions(g, path, visitedMask, ignoredMask)) {
                /// DEBUG:
//                cout << "[dfsInducedCycleMask] Cycle was forced: ";
//                for (auto v: path) cout << v << " ";
//                cout << "\n";
                found = true;

                if (maxCycleLen >= cutoff) {
                    foundMaxBound = true;
                    return;
                }
            }

            // Safe to extend the path with nb
            path.push_back(nb);
            setBit(visitedMask, nb);

            /// DEBUG:
//            cout << "[dfsInducedCycleMask] adding " << nb << " to path" << endl;
//            printIgnoredMask(ignoredMask,g.V);

            // Add other neighbours to ignore
            vector<int> ignoredNbrs;
            for (int n : g.adj[current]) {
//                cout << "[dfsInducedCycleMask] looking at neighbour " << n << " of current " << current << ", deciding if ignore" << endl;
                if (n != nb && !isSet(ignoredMask, n) && !isSet( visitedMask, n)) {
                    setBit(ignoredMask, n);
                    ignoredNbrs.push_back(n);
//                    cout << "[dfsInducedCycleMask] adding " << n << " to ignore (other neighbour)" << endl;
                }
            }

            if (!found) {
                int newCurrent = path.back();
                int newParent = (path.size() >= 2) ? path[path.size() - 2] : -1;
                dfsInducedCycleMaskGeneral(g, newCurrent, newParent,
                                           path, visitedMask, ignoredMask, cutoff);
            }

            if (foundMaxBound) return;

            // Backtrack: remove nb from path and visitedMask
            while (path.front() != front) {
                /// DEBUG:
//                cout << "[dfsInducedCycleMask]  removing " << path.front() << " from path" << endl;
                clearBit(visitedMask, path.front());
                path.pop_front();
            }
            int removed = path.back();
            path.pop_back();
            clearBit(visitedMask, removed);
            for (int n : ignoredNbrs) {
                clearBit(ignoredMask, n);
            }

            /// DEBUG:
//            cout << "[dfsInducedCycleMask]  did not found max bound, current path: ";
//            for (auto v : path) cout << v << " ";
//            cout << "; removing " << removed << " and from ignore: "; for (auto v : ignoredNbrs) cout << v << ", " << endl;
            ignoredNbrs.clear();
        }
    }
}

int inducedCycleUpperBound(int n, int d) {
    if (d <= 1) return 0;          // no cycles in 0/1-regular (except trivial stuff)
    // formula: floor( d / (2(d-1)) * n )
    return (d * n) / (2 * (d - 1));
}

// Public wrapper for the general algorithm.
vector<int> findInducedCycleMaskGeneral(Graph &g, int d)
{
    bestCycle.clear();
    maxCycleLen = 0;
    foundMaxBound = false;

    /// NOTE: For reading multiple graphs from file
    bannedMask = 0ULL;

    int initialCutoff = inducedCycleUpperBound(g.V, d);
//    cout << "Upper limit is: " << initialCutoff << endl;

    for (int start = 0; start < g.V; ++start) {
        if (foundMaxBound) break;

        if (g.V - start < maxCycleLen) {
            /// DEBUG:
//            cout << "[findInducedCycleMask] Breaking early at vertex " << start << " (remaining vertices too few).\n";
            break;
        }

        uint64_t visitedMask = 0ULL;
        uint64_t ignoredMask = 0ULL;

        setBit(visitedMask, start);
        deque<int> path;
        path.push_back(start);

        /// DEBUG:
//        cout << "\n[findInducedCycleMask] Starting new DFS from vertex "
//             << start << "...\n";

        dfsInducedCycleMaskGeneral(g, start, -1, path,
                            visitedMask, ignoredMask, initialCutoff);

        if (maxCycleLen == initialCutoff) {
            foundMaxBound = true;
        }

        setBit(bannedMask, start);
    }

    return bestCycle;
}

/// NOTE: for reading one graph from terminal
int main() {
   int numVertices;
   cout << "Enter the graph:";
   cin >> numVertices;
   cin.ignore(); // consume the end of line

   Graph g(numVertices);
   g.inputGraph();

   if (!g.isRegular()) {
       cerr << "Error: input graph is not regular (degrees are not uniform)." << endl;
       return 1;
   }

   int d = g.degree();
   cout << "Detected regular degree d = " << d << "\n";

   auto startTime = high_resolution_clock::now();

   vector<int> inducedCycle;

   // For now, always use the general solver.
   inducedCycle = findInducedCycleMaskGeneral(g, d);

   auto endTime = high_resolution_clock::now();
   auto duration = duration_cast<milliseconds>(endTime - startTime);
   cout << "Execution time: " << duration.count() << " ms\n";

   if (!inducedCycle.empty()) {
       cout << "Longest Induced Cycle (length " << inducedCycle.size() << "): ";
       for (int v : inducedCycle) {
           cout << v << " ";
       }
       cout << "\n";
   } else {
       cout << "No induced cycle found.\n";
   }

   return 0;
}


/// NOTE: for reading multile graphs from a file

// Expect stem like "4_9_tests"
static bool parseRegVFromStem(const std::string& stem, int& reg, int& Vhint) {
    size_t p1 = stem.find('_');
    if (p1 == std::string::npos) return false;
    size_t p2 = stem.find('_', p1 + 1);
    if (p2 == std::string::npos) return false;
    try {
        reg   = std::stoi(stem.substr(0, p1));
        Vhint = std::stoi(stem.substr(p1 + 1, p2 - (p1 + 1)));
        return true;
    } catch (...) {
        return false;
    }
}
//
//int main() {
//    const std::string INPUT_FILE =
//            "C:\\Users\\elisk\\Documents\\GitHub\\1.mAIN\\diplomovka\\helpers\\graphs_for_testing\\6_12_tests.asc";
//
//    fs::path inPath = fs::absolute(INPUT_FILE);
//    std::ifstream in(inPath);
//    if (!in) {
//        std::cerr << "Cannot open " << inPath << "\n";
//        return 1;
//    }
//
//    std::string stem = inPath.stem().string(); // e.g. "4_9_tests"
//    int REG = 0, V_from_name = 0;
//    if (!parseRegVFromStem(stem, REG, V_from_name)) {
//        std::cerr << "Filename stem must look like <reg>_<V>_... (e.g. 4_9_tests)\n";
//        std::cerr << "Got stem: " << stem << "\n";
//        return 1;
//    }
//
//    fs::path graphsDir   = inPath.parent_path();
//    fs::path resultsRoot = graphsDir / "test_results";
//    fs::path regDir      = resultsRoot / (std::to_string(REG) + "_regular");
//
//    int graphNr = 0;
//    std::string line;
//
//    // We may not know V until we read the first graph block.
//    int V_for_folder = V_from_name;
//
//    // We'll open the summary output after we know V (from the first graph).
//    std::ofstream summaryOut;
//    fs::path summaryPath;
//
//    auto openSummaryIfNeeded = [&](int V) {
//        if (summaryOut.is_open()) return;
//        V_for_folder = V;
//
//        fs::path vDir = regDir / (std::to_string(V_for_folder) + "_vertices");
//        fs::create_directories(vDir);
//
//        summaryPath = vDir / (stem + "_fast_summary.txt");
//        summaryOut.open(summaryPath);
//        if (!summaryOut) {
//            std::cerr << "Cannot create " << summaryPath << "\n";
//            std::exit(1);
//        }
//
//        summaryOut << "Input file: " << inPath.string() << "\n";
//        summaryOut << "Regularity (from filename): " << REG << "\n";
//        summaryOut << "Vertices (from first graph): " << V_for_folder << "\n\n";
//    };
//
//    while (true) {
//        // ---- seek next "Graph" header ----
//        do {
//            if (!std::getline(in, line)) {
//                if (summaryOut.is_open()) {
//                    summaryOut << "\nProcessed graphs: " << graphNr << "\n";
//                }
//                std::cout << "Processed " << graphNr << " graphs.\n";
//                if (summaryOut.is_open()) {
//                    std::cout << "→ wrote summary: " << summaryPath << "\n";
//                }
//                return 0; // EOF
//            }
//        } while (line.rfind("Graph", 0) != 0); // "Graph 1:" etc.
//
//        std::string graphHeader = line;
//
//        // ---- read Min Edge Cut line + Girth line ----
//        std::string minCutLine, girthLine;
//        if (!std::getline(in, minCutLine)) break;
//        if (!std::getline(in, girthLine)) break;
//
//        // ---- read vertex count line ----
//        int V = 0;
//        {
//            std::string vLine;
//            if (!std::getline(in, vLine)) break;
//            std::stringstream ss(vLine);
//            if (!(ss >> V)) {
//                std::cerr << "Bad format: expected vertex count after header, got: " << vLine << "\n";
//                return 1;
//            }
//        }
//
//        openSummaryIfNeeded(V);
//
//        if (V > 64) {
//            summaryOut << "Graph #" << "\n";
//            summaryOut << graphHeader << "\n" << minCutLine << "\n" << girthLine << "\n";
//            summaryOut << "Vertices: " << V << "\n";
//            summaryOut << "SKIPPED: V > 64 (algorithm uses uint64_t masks)\n\n";
//
//            // skip adjacency lines
//            for (int i = 0; i < V; ++i) std::getline(in, line);
//            ++graphNr;
//            continue;
//        }
//
//        // ---- build graph ----
//        Graph g(V);
//
//        for (int i = 0; i < V; ++i) {
//            if (!std::getline(in, line)) {
//                std::cerr << "Unexpected EOF while reading adjacency.\n";
//                return 1;
//            }
//            if (line.empty()) { --i; continue; } // tolerate blank lines
//
//            std::stringstream ss(line);
//            for (int j = 0; j < REG; ++j) {
//                int nb;
//                if (!(ss >> nb)) {
//                    std::cerr << "Bad adjacency line for vertex " << i
//                              << " (expected " << REG << " ints): " << line << "\n";
//                    return 1;
//                }
//                g.addEdge(i, nb);
//            }
//        }
//
//        ++graphNr;
//
//        // ---- run your algorithm ----
//        auto t0 = steady_clock::now();
//        std::vector<int> best = findInducedCycleMaskGeneral(g, REG);
//        auto t1 = steady_clock::now();
//
//        auto us2 = duration_cast<microseconds>(t1 - t0).count();
//        double ms = us2 / 1000.0;
//
//        // ---- append to summary ----
//        summaryOut << graphHeader << "\n" << minCutLine << "\n" << girthLine << "\n";
//        summaryOut << "Vertices: " << V << "\n";
//        summaryOut << "Regularity: " << REG << "\n";
//        summaryOut << "Algorithm time: " << ms << " ms\n";
//
//        if (best.empty()) {
//            summaryOut << "No induced cycle found.\n\n";
//        } else {
//            summaryOut << "Longest induced cycle length = " << best.size() << "\n";
//            summaryOut << "Cycle: ";
//            for (int v : best) summaryOut << v << " ";
//            summaryOut << "\n\n";
//        }
//    }
//
//    return 0;
//}

/// NOTE: reading one folder, each *.asc in it, each graph in each file and writes it all into one big csv for ML project

// Parse a line like "Min Edge Cut:  2" or "Girth: 3" into the integer after the colon.
// Returns -1 if it cannot parse anything.
static int parseIntAfterColon(const std::string& line) {
    // find the colon
    size_t pos = line.find(':');
    if (pos == std::string::npos) {
        return -1;
    }

    // take substring after colon
    std::string num = line.substr(pos + 1);

    // trim leading/trailing whitespace
    size_t start = num.find_first_not_of(" \t\r\n");
    if (start == std::string::npos) {
        return -1;
    }
    size_t end = num.find_last_not_of(" \t\r\n");
    num = num.substr(start, end - start + 1);

    try {
        return std::stoi(num);
    } catch (...) {
        return -1;
    }
}

// Build a symmetric adjacency matrix for convenience.
static std::vector<std::vector<bool>> buildAdjMatrix(const Graph &g) {
    std::vector<std::vector<bool>> mat(g.V, std::vector<bool>(g.V, false));
    for (int u = 0; u < g.V; ++u) {
        for (int v : g.adj[u]) {
            mat[u][v] = true;
            mat[v][u] = true;
        }
    }
    return mat;
}

// Count (undirected) triangles in g.
static int countTriangles(const Graph &g) {
    auto mat = buildAdjMatrix(g);
    int V = g.V;
    int tri = 0;
    for (int i = 0; i < V; ++i) {
        for (int j = i + 1; j < V; ++j) {
            if (!mat[i][j]) continue;
            for (int k = j + 1; k < V; ++k) {
                if (mat[i][k] && mat[j][k]) {
                    ++tri;
                }
            }
        }
    }
    return tri;
}

// Count induced 4-cycles (C4) in g.
static int countInducedC4(const Graph &g) {
    auto mat = buildAdjMatrix(g);
    int V = g.V;
    long long cnt = 0;

    for (int a = 0; a < V; ++a) {
        for (int b = 0; b < V; ++b) {
            if (b == a) continue;
            for (int c = 0; c < V; ++c) {
                if (c == a || c == b) continue;
                for (int d = 0; d < V; ++d) {
                    if (d == a || d == b || d == c) continue;

                    // edges of the 4-cycle a-b-c-d-a
                    if (mat[a][b] && mat[b][c] && mat[c][d] && mat[d][a]) {
                        // induced: no diagonals a-c or b-d
                        if (!mat[a][c] && !mat[b][d]) {
                            ++cnt;
                        }
                    }
                }
            }
        }
    }

    // each undirected cycle counted 8 times (4 rotations * 2 directions)
    return static_cast<int>(cnt / 8);
}

// Compute graph diameter and average shortest path length.
static void computeDistances(const Graph &g, int &diameter, double &avgDist) {
    int V = g.V;
    const int INF = 1e9;
    std::vector<std::vector<int>> dist(V, std::vector<int>(V, INF));

    diameter = 0;
    long long sum = 0;
    long long pairs = 0;

    for (int s = 0; s < V; ++s) {
        std::queue<int> q;
        dist[s][s] = 0;
        q.push(s);

        while (!q.empty()) {
            int u = q.front(); q.pop();
            for (int v : g.adj[u]) {
                if (dist[s][v] == INF) {
                    dist[s][v] = dist[s][u] + 1;
                    q.push(v);
                }
            }
        }

        for (int t = 0; t < V; ++t) {
            if (t == s) continue;
            if (dist[s][t] < INF) {
                sum += dist[s][t];
                ++pairs;
                if (dist[s][t] > diameter) {
                    diameter = dist[s][t];
                }
            }
        }
    }

    avgDist = (pairs > 0) ? (static_cast<double>(sum) / pairs) : 0.0;
}


// Process a single .asc file and append rows to the global CSV.
void processAscFile(const fs::path& inPath, std::ofstream& csvOut) {
    std::ifstream in(inPath);
    if (!in) {
        std::cerr << "Cannot open " << inPath << "\n";
        return;
    }

    std::string stem = inPath.stem().string(); // e.g. "4_9_tests"
    int REG = 0, V_from_name = 0;
    if (!parseRegVFromStem(stem, REG, V_from_name)) {
        std::cerr << "Skipping " << inPath << " (bad filename stem: " << stem << ")\n";
        return;
    }

    std::cout << "Processing file: " << inPath << " (reg=" << REG << ")\n";

    std::string line;
    int graphNr = 0;

    while (true) {
        // ---- seek next "Graph" header ----
        do {
            if (!std::getline(in, line)) {
                std::cout << "  Processed " << graphNr << " graphs in " << inPath.filename() << "\n";
                return; // EOF
            }
        } while (line.rfind("Graph", 0) != 0); // line starts with "Graph"

        std::string graphHeader = line;

        // ---- read Min Edge Cut line + Girth line ----
        std::string minCutLine, girthLine;
        if (!std::getline(in, minCutLine)) break;
        if (!std::getline(in, girthLine)) break;

        int minEdgeCut = parseIntAfterColon(minCutLine);
        int girth      = parseIntAfterColon(girthLine);

        // ---- read vertex count line ----
        int V = 0;
        {
            std::string vLine;
            if (!std::getline(in, vLine)) break;
            std::stringstream ss(vLine);
            if (!(ss >> V)) {
                std::cerr << "Bad format in " << inPath << ": expected vertex count after header, got: " << vLine << "\n";
                return;
            }
        }

        // skip graphs that are too big for uint64_t masks
        if (V > 64) {
            std::cerr << "  Skipping graph (V>64) in " << inPath << "\n";
            // skip adjacency lines
            for (int i = 0; i < V; ++i) std::getline(in, line);
            ++graphNr;
            continue;
        }

        // ---- build graph ----
        Graph g(V);

        for (int i = 0; i < V; ++i) {
            if (!std::getline(in, line)) {
                std::cerr << "Unexpected EOF while reading adjacency in " << inPath << "\n";
                return;
            }
            if (line.empty()) { --i; continue; } // tolerate blank lines

            std::stringstream ss(line);
            for (int j = 0; j < REG; ++j) {
                int nb;
                if (!(ss >> nb)) {
                    std::cerr << "Bad adjacency line for vertex " << i
                              << " (expected " << REG << " ints) in " << inPath
                              << ": " << line << "\n";
                    return;
                }
                g.addEdge(i, nb);
            }
        }

        ++graphNr;

        int triCount = countTriangles(g);
        int c4Count  = countInducedC4(g);
        int diam     = 0;
        double avgDist = 0.0;
        computeDistances(g, diam, avgDist);

        // ---- run your algorithm ----
        auto t0 = steady_clock::now();
        std::vector<int> best = findInducedCycleMaskGeneral(g, REG);
        auto t1 = steady_clock::now();

        auto us2 = duration_cast<microseconds>(t1 - t0).count();
        double ms = us2 / 1000.0;

        int longestLen = static_cast<int>(best.size());

        // ---- append to global CSV ----
        csvOut << inPath.filename().string() << ","
               << stem << ","
               << REG << ","
               << V << ","
               << graphNr << ","
               << minEdgeCut << ","
               << girth << ","
               << ms << ","
               << longestLen << ","
               << triCount << ","
               << c4Count << ","
               << diam << ","
               << avgDist << "\n";
    }

    std::cout << "  Processed " << graphNr << " graphs in " << inPath.filename() << "\n";
}

// int main() {
//     // TODO: change this to your actual folder with all the .asc files
//     const std::string INPUT_DIR =
//             "C:\\Users\\elisk\\Documents\\GitHub\\1.mAIN\\diplomovka\\helpers\\graphs_dataset\\large_graphs";

//     fs::path inputDir = fs::absolute(INPUT_DIR);

//     if (!fs::exists(inputDir) || !fs::is_directory(inputDir)) {
//         std::cerr << "Input directory does not exist or is not a directory: " << inputDir << "\n";
//         return 1;
//     }

//     // results directory inside the dataset folder
//     fs::path resultsDir = inputDir / "results_large";
//     fs::create_directories(resultsDir);

//     // one global CSV for all graphs from all files
//     fs::path csvPath = resultsDir / "all_large_graphs_dataset.csv";
//     std::ofstream csvOut(csvPath);
//     if (!csvOut) {
//         std::cerr << "Cannot create CSV file: " << csvPath << "\n";
//         return 1;
//     }

//     // header
//     csvOut << "input_file,stem,regularity,vertices,graph_index,"
//            << "min_edge_cut,girth,algo_time_ms,longest_cycle_len,"
//            << "triangles,c4_induced,diameter,avg_distance\n";

//     // iterate over all .asc files in the directory
//     int filesProcessed = 0;
//     for (const auto& entry : fs::directory_iterator(inputDir)) {
//         if (!entry.is_regular_file()) continue;
//         fs::path p = entry.path();
//         if (p.extension() != ".asc") continue;

//         processAscFile(p, csvOut);
//         ++filesProcessed;
//     }

//     std::cout << "Done. Processed " << filesProcessed << " .asc files.\n";
//     std::cout << "Global CSV written to: " << csvPath << "\n";

//     return 0;
// }
