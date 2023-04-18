#include <functional> // std::function
#include <sstream>    // std::stringstream
#include <list>
#include <set>
#include <map>


using std::set;
using std::map;
using std::pair;
using std::list;
using std::string;
using std::function;
using std::stringstream;


template<typename indx_t>
indx_t DefaultIndex();


template<typename indx_t>
indx_t NextIndex(indx_t);


template<typename indx_t>
struct work_t {
    indx_t id;
    set<indx_t> required;
    float t_min;
    float t_max;
    //float c_min;
    //float c_max;
    //float k;
    //float b;
};


template<typename indx_t>
class Graph {
public:

    using link_t = pair<indx_t, indx_t>;
    using edge_t = pair<link_t, indx_t>;
    using work_t = work_t<indx_t>;

    list<indx_t> nodes;
    map<link_t, indx_t> edges;

    operator string() {
        stringstream buf;

        for (typename Graph<indx_t>::edge_t edge : edges) {
            typename Graph<indx_t>::link_t link = edge.first;
            buf << link.first << " -> " << link.second;
            if (!edge_empty(link)) buf << ' ' << edge.second;
            buf << '\n';
        }

        return buf.str();
    }

    bool is_parent_node(const indx_t& node) const {
        auto comp = [&node](const edge_t& edge) { return edge.first.first == node; };
        return std::find_if(edges.begin(), edges.end(), comp) != edges.end();
    }

    bool is_child_node(const indx_t& node) const {
        auto comp = [&node](const edge_t& edge) { return edge.first.second == node; };
        return std::find_if(edges.begin(), edges.end(), comp) != edges.end();
    }

    bool edge_exists(const link_t& link) const {
        return edges.find(link) != edges.end();
    }

    bool edge_empty(const link_t& link) const {
        return edge_exists(link) && edges.at(link) == DefaultIndex<indx_t>();
    }

    indx_t shared_parent(indx_t node1, indx_t node2) const {
        for (const edge_t& edge1 : edges) {
            if (edge1.first.second != node1) continue;
            if (edge_empty(edge1.first)) continue;

            for (const edge_t& edge2 : edges) {
                if (edge2.first.second != node2) continue;
                if (edge1.first.first == edge2.first.first) return edge1.first.first;
            }
        }
        return DefaultIndex<indx_t>();
    }

    // Оптимизирует граф, удаляет дополнительные работы по максимуму
    void optimize() {
        using std::next;
        using std::prev;

        size_t nodes_count;

        do {
            nodes_count = nodes.size();

            for (auto it = next(nodes.begin()); it != prev(nodes.end()); it++) {
                // Рассматриваются 3 подряд идущих узла: A B C
                // Узел B считается лишним, если:
                //      1) Работ BC дополнительная, а работы AC не существует
                //      2) Работа AC и BC дополнительные, а работа AC существует
                // 
                // Узел B нельзя удалять, если узлы B и C имеют общий родительский узел.
                // Исключением является последний из всех узлов.
                indx_t a = *prev(it);
                indx_t b = *it;
                indx_t c = *next(it);
                indx_t a0 = shared_parent(b, c);

                bool bc_empty = edge_empty(link_t{ b, c });
                bool ab_empty = edge_empty(link_t{ a, b });
                bool ac_exists = edge_exists(link_t{ a, c });
                bool b_and_c_have_shared_parent = (a0 != DefaultIndex<indx_t>());
                bool c_last_node = (next(it) == prev(nodes.end()));

                if ((!b_and_c_have_shared_parent || c_last_node) && 
                    ((bc_empty && !ac_exists) || (ab_empty && bc_empty && ac_exists)))
                {
                    it = prev(it);
                    nodes.erase(next(it));

                    auto begin = edges.begin();
                    auto end = edges.end();

                    while (begin != end) {
                        begin++;

                        indx_t work_id = prev(begin)->second;
                        link_t link = prev(begin)->first;
                        link_t new_link;

                        if (link.first == b) new_link = link_t{ c, link.second };
                        else if (link.second == b) new_link = link_t{ link.first, c };
                        else if (link.second == link.first) new_link = link;
                        else continue;

                        if (!edge_exists(new_link) || edge_empty(new_link)) edges[new_link] = work_id;
                        edges.erase(link);
                        
                    }
                }

                // Связь BC можно переписать, если связь BC дополнительная, а у B и C есть общий родитель
                else if (bc_empty && b_and_c_have_shared_parent) {
                    if (edge_exists(link_t{ b, c })) {
                        edges[link_t{ b, c }] = edges[link_t{ a0, c }];
                        edges.erase(link_t{ a0, c });
                    }
                }
            }

        } while (nodes_count == nodes.size());

        // Узлы без связей удаляются
        for(auto begin = nodes.begin(); begin != nodes.end();) {
            auto next_begin = next(begin);
            if (!is_child_node(*begin) && !is_parent_node(*begin)) nodes.erase(begin);
            begin = next_begin;
        }

        // Связи с блокировками в себя удаляются 
        for (auto begin = edges.begin(); begin != edges.end();) {
            auto next_begin = next(begin);
            const link_t& link = begin->first;
            if (link.first == link.second) edges.erase(link);
            begin = next_begin;
        }
    }

    // Создает граф для списка работ
    template<class WorkIt>
    void assign_nodes_by_works(WorkIt wbegin, WorkIt wend, indx_t first_node = DefaultIndex<indx_t>()) {
        using std::next;
        using std::advance;
        using std::distance;
        using std::make_reverse_iterator;

        // Чтобы все события были связаны между собой, необходимо провести "цепочку" из N событий,
        // Где N это количество работ + 1
        nodes.push_back(first_node);
        for (size_t i = 0; i < distance(wbegin, wend); i++) {
            indx_t second_node = NextIndex(first_node);
            nodes.push_back(second_node);
            edges[link_t{ first_node, second_node }] = { DefaultIndex<indx_t>() };
            first_node = second_node;
        }

        // Чтобы провести работу AB нужно, чтобы 
        //      1) Событие B было j-тым по счету, где j это порядковый номер работы + 1
        //      2) Событие A было i-тым по счету, где i это порядковый номер самого последнего (по порядку) необходимого события
        for (auto begin = wbegin; begin != wend; begin++) {
            const work_t& work = *begin;

            size_t j = distance(wbegin, next(begin));
            size_t i = 0;
            
            auto rbegin = make_reverse_iterator(begin);
            auto rend = make_reverse_iterator(wbegin);
            while (rbegin != rend) {
                const indx_t& id = rbegin->id;
                if (work.required.find(id) != work.required.end()) {
                    i = distance(rbegin, rend);
                    break;
                }
                rbegin++;
            }

            auto first_node_it = nodes.begin();
            advance(first_node_it, i);

            auto second_node_it = nodes.begin();
            advance(second_node_it, j);

            edges[link_t{ *first_node_it, *second_node_it }] = work.id;
        }
    }

    // Расчитывает критический путь
    template<class WorkIt, class IndxIt>
    IndxIt critical_path(WorkIt wbegin, WorkIt wend, IndxIt dest) {

        float max_sum = 0;
        list<indx_t> full_path;
        
        // вытаскивание времени пути из списка работ
        function<float(indx_t)> t_max_of = [&wbegin, wend](indx_t work_id) {
            for (auto begin = wbegin; begin != wend; begin++)
                if (begin->id == work_id) return begin->t_max;
            return 0.f;
        };

        // рекурсивная функция 
        // проходится по каждому узлу, запоминая путь и "время" пути
        function<void(list<indx_t>, float)> f;
        f = [&max_sum, &full_path, this, &f, &t_max_of](list<indx_t> path, float sum) {
            indx_t last_node = path.back();

            // самый долгий путь записывается в full_path
            if (last_node == nodes.back()) {
                if (sum > max_sum) {
                    max_sum = sum;
                    full_path = path;
                }
                return;
            }

            // для каждого дочернего узла создается своя ветка рекурсии
            for (const edge_t& edge : edges) {
                const link_t& link = edge.first;
                const indx_t& work = edge.second;
                if (link.first == last_node) {
                    path.push_back(link.second);
                    f(path, sum + t_max_of(work));
                }
            }
        };

        f({ nodes.front() }, 0);

        return std::copy(full_path.begin(), full_path.end(), dest);
    }

};


template<>
char DefaultIndex() {
    return '0';
}


template<>
char NextIndex(char i) {
    return i + 1;
}



int main()
{
    // вр 8
    list<work_t<char>> works{
        {'1',   {},               4,  7 },
        {'2',   {},               8,  11},
        {'3',   {},               3,  5 },
        {'4',   {'1'},            7,  10},
        {'5',   {'1', '2', '3'},  1,  4 },
        {'6',   {'3'},            9,  13},
        {'7',   {'3', '4', '5'},  8,  12},
        {'8',   {'4'},            5,  8 },
    };

    // создаем граф 
    Graph<char> graph;
    graph.assign_nodes_by_works(works.begin(), works.end(), 'A');

    printf(string(graph).c_str());
    printf("\n");

    // оптимизируем граф
    graph.optimize();

    printf(string(graph).c_str());
    printf("\n");

    // поиск критического пути
    list<char> critical_path(graph.nodes.size()); // контейнер для критического пути (создается с запасом места)
    auto path_end = graph.critical_path(works.begin(), works.end(), critical_path.begin()); 
    critical_path.erase(path_end, critical_path.end()); // удаление запасных элементов из контейнера

    stringstream buf;
    for (auto node : critical_path) buf << node << ' ';
    printf(buf.str().c_str());

    return 0;
}
