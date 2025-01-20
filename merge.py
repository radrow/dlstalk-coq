#!/usr/bin/python
import argparse
import re
import os
from pathlib import Path


NODE_REG = re.compile(
    r'N: '
    r'(?P<id>[0-9]+) '
    r'"(?P<name>[a-zA-Z0-9\-_\']+)" '
    r'\['
    r'(?:body=(?P<body>[a-z]+),)? *'
    r'kind=(?P<kind>[a-z]+), *'
    r'prop=(?P<prop>[a-z]+), *'
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
        s += f'path="{self.path[-1]}", ' if self.path else ''
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


def reduce(nodes, edges):
    new_nodes = []
    merge = {}  # (name, module) => id
    replace = {}  # id => id
    teresting = set()  # so I can write "in teresting"

    for n in nodes:
        if not n.path or n.path[0] != 'Deps':
            continue

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


def generate(filename, layout='dot', defs=False, trans=False):
    input_path = filename
    dpd_path = input_path.with_stem(input_path.stem + "_reduced")
    dot_path = input_path.with_suffix(".dot")
    svg_path = input_path.with_suffix(".svg")

    with open(input_path) as f:
        lines = [line for line in f]

    nodes, edges = parse(lines)

    new_nodes, new_edges = reduce(nodes, edges)

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

    args = parser.parse_args()

    generate(**args.__dict__)


if __name__ == "__main__":
    main()
