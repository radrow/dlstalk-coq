#!/usr/bin/python
import graphlib
import argparse
import re
import os
from pathlib import Path


NODE_REG = re.compile(
    r'N: '
    r'(?P<id>[0-9]+) '
    r'"(?P<name>[^"]+)" '
    r'\[ *'
    r'(?:body=(?P<body>[a-z]+),)? *'
    r'kind=(?P<kind>[a-z]+), *'
    r'(prop=(?P<prop>[a-z]+),)? *'
    r'(?:path="(?P<path>[^"]+)",)? *'
    r'\];'
)

EDGE_REG = re.compile(
    r'E: '
    r'(?P<source>[0-9]+) '
    r'(?P<target>[0-9]+) '
    r'\[weight=(?P<weight>[0-9]+),? *\];'
)


class Node:
    def __init__(self, **kwargs):
        self.__dict__ = kwargs

    def parse(s):
        n = re.match(NODE_REG, s)
        if not n:
            print(f"Chuj kurwa: {s}")

        d = dict(
            i=int(n['id']),
            name=n['name'],
            body=n['body'] == 'yes',
            kind=n['kind'],
            prop=n['prop'] == 'yes',
            path=n['path'].split('.') if n['path'] else None,
        )
        return Node(**d)

    def __repr__(self):
        s = ""
        s += f'N: {self.i} "{self.name}" '
        s += '['
        s += f'body={"yes" if self.body else "no"}, ' if self.body else ''
        s += f'kind={self.kind}, ' if self.kind else ''
        s += f'prop={"yes" if self.prop else "no"}, ' if self.prop else ''
        s += f'path="{".".join(self.path)}", ' if self.path else ''
        s += '];'
        return s


class Edge:
    def __init__(self, **kwargs):
        self.__dict__ = kwargs

    def parse(s):
        n = re.match(EDGE_REG, s)
        d = dict(
            source=int(n['source']),
            target=int(n['target']),
            weight=int(n['weight']),
        )
        return Edge(**d)

    def __repr__(self):
        return f"E: {self.source} {self.target} [weight={self.weight}, ];"


def parse(lines):
    nodes = []
    edges = []

    for line in lines:
        if line[0] == 'N':
            n = Node.parse(line)
            nodes.append(n)

        elif line[0] == 'E':
            e = Edge.parse(line)
            edges.append(e)

    return nodes, edges


def mk_idmap(nodes):
    idmap = {}

    for n in nodes:
        idmap[n.i] = n

    return idmap


def mk_graph(nodes, edges):
    graph = {}
    for n in nodes:
        graph[n.i] = []

    for e in edges:
        graph[e.source].append(e.target)

    return graph


def toposort(nodes, edges, group=False):
    idmap = mk_idmap(nodes)
    graph = mk_graph(nodes, edges)

    ts = graphlib.TopologicalSorter(graph)
    groups = []

    ts.prepare()
    while ts.is_active():
        node_group = ts.get_ready()
        groups.append([idmap[i] for i in node_group])
        ts.done(*node_group)

    for i, ns in enumerate(groups):
        g = len(groups) - i - 1
        for n in ns:
            if group:
                if n.path:
                    n.path.append(f"G{g}")
                else:
                    n.path = [f"G{g}"]
            yield n


def mk_org_list(nodes, edges):
    from itertools import groupby

    idmap = mk_idmap(nodes)
    graph = mk_graph(nodes, edges)

    nodes = sorted(nodes, key=lambda n: '.'.join(n.path))
    ms = list((g, list(ns)) for (g, ns) in groupby(nodes, key=lambda n: n.path[0]))
    ms = sorted(ms, key=lambda m: min([n.path[1] for n in m[1]]))
    for g, ns in ms:
        print(f"** {g}\n")
        for gg, nns in groupby(ns, key=lambda n: int(n.path[1][1:])):
            print(f"*** {gg}\n")
            for n in sorted(nns, key=lambda n: n.i):
                if n.kind == 'cnst' and n.prop and n.body:
                    print(f"**** {n.name}\n")
                    for ii in graph[n.i]:
                        nn = idmap[ii]
                        if nn.kind == 'cnst' and nn.prop and nn.body:
                            print(f"- ~{idmap[ii].name}~")
                    print("")


def reduce(nodes, edges):
    new_nodes = []
    merge = {}  # (name, module) => id
    replace = {}  # id => id
    teresting = set()  # so I can write "in teresting"

    for n in nodes:
        if not n.path or n.path[0] != 'Deps':
            continue

        n.path = n.path[-1:]

        teresting.add(n.i)

        key = (n.path[-1], n.name)

        if key in merge:
            # print(f"Replacing {n.i} with {merge[key]} ({key})")
            replace[n.i] = merge[key]
        else:
            merge[key] = n.i
            new_nodes.append(n)

    edgemap = {}  # (src, target) => weight

    for e in edges:
        if e.source not in teresting or e.target not in teresting:
            continue

        key = (replace.get(e.source, e.source),
               replace.get(e.target, e.target)
               )

        if key[0] == key[1]:  # There are no cycles originally
            continue

        if key in edgemap:
            edgemap[key] = edgemap[key] + e.weight
        else:
            edgemap[key] = e.weight

    new_edges = []
    for ((s, t), w) in edgemap.items():
        new_edges.append(Edge(source=s, target=t, weight=w))

    return new_nodes, new_edges


def graph_name(f):
    return re.sub(r'[\-.]+', '', f.stem)


def load_file(filename):
    with open(filename) as f:
        lines = [line for line in f]

    return parse(lines)


def generate(filename, layout='dot', defs=False, trans=False, group=False):
    input_path = filename
    dpd_path = input_path.with_stem(input_path.stem + "_reduced")
    dot_path = input_path.with_suffix(".dot")
    svg_path = input_path.with_suffix(".svg")

    nodes, edges = load_file(input_path)

    new_nodes, new_edges = reduce(nodes, edges)

    new_nodes = list(toposort(new_nodes, new_edges, group))

    with open(dpd_path, "w") as f:
        for n in new_nodes:
            f.write(str(n) + "\n")

        for e in new_edges:
            f.write(str(e) + "\n")

    print("DPD reduced. "
          f"Total nodes: {len(new_nodes)} (from {len(nodes)}),"
          f"edges: {len(new_edges)} (from {len(edges)})"
          )

    DPD2_DOT_CMD = (
        f'dpd2dot {dpd_path} '
        f'-o {dot_path} '
        f'-graphname {graph_name(input_path)} '
        f'{"-without-defs" if not defs else ""} '
        f'{"-keep-trans" if trans else ""} '
    )

    print("Running", DPD2_DOT_CMD)
    if os.system(DPD2_DOT_CMD) != 0:
        return

    DOT_CMD = f"dot {dot_path} -o {svg_path} -Tsvg -K{layout}"

    print("Running", DOT_CMD)
    if os.system(DOT_CMD) != 0:
        return

    print("Done")


def main():
    parser = argparse.ArgumentParser(description="Simplifier of DPD.")
    parser.add_argument("filename", type=Path, help="Original DPD")
    parser.add_argument("--layout", type=str, default='dot', help="DOT layout")
    parser.add_argument("--defs", action='store_true', default=False, help="Include non-Prop definitions")
    parser.add_argument("--trans", action='store_true', default=False, help="Include transitive dependencies")
    parser.add_argument("--group", action='store_true', default=False, help="Group SCC")

    args = parser.parse_args()

    generate(**args.__dict__)


if __name__ == "__main__":
    main()
