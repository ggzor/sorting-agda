import dataclasses
from attrdict import AttrDict

from enum import Enum, auto
import collections.abc
from pathlib import Path
from typing import Dict, List, Literal, Union
from pprint import pprint
from re import compile


class State(Enum):
    TITLE = auto()
    ABSTRACT = auto()
    GENERIC = auto()
    HEADING = auto()
    NON_HEADING = auto()


class LookaheadIterator(collections.abc.Iterator):
    def __init__(self, base):
        self.prev = None
        self.base = base

    def __next__(self):
        if self.prev is None:
            return next(self.base)
        else:
            tmp, self.prev = self.prev, None
            return tmp

    def lookahead(self):
        if self.prev is None:
            self.prev = next(self.base)
            return self.prev
        else:
            return self.prev


from dataclasses import dataclass, field
from itertools import dropwhile


@dataclass
class CodeReference:
    file: Path
    start: int
    end: int


@dataclass
class CodeBlock:
    text: str
    hidden: bool


@dataclass
class TextNode:
    text: str


@dataclass
class Section:
    title: str
    parts: List[Union[TextNode, CodeReference]] = field(default_factory=list)


@dataclass
class LangResult:
    title: str = ""
    abstract: str = ""
    sections: List[Section] = field(default_factory=list)


def is_node_of_type(node: Union[TextNode, CodeReference], ty: Literal[""]):
    return ty in str(type(node))


FILE_INFO_REGEX = compile(r"([^:]+):(\d+)-(\d+)")


def first_pass(source_path: Path, langs: List[str]):
    import mistune

    markdown = mistune.create_markdown(renderer=mistune.AstRenderer())
    source = source_path.read_text(encoding="utf8")

    source_data = list(map(AttrDict, markdown(source)))

    result = {l: LangResult() for l in langs}

    state = State.TITLE
    it = LookaheadIterator(iter(source_data))
    try:
        while True:
            if it.lookahead().type == "block_html":
                next(it)
                continue

            if state == State.TITLE:
                for l in langs:
                    result[l].title = next(it).children[0].text
                state = State.ABSTRACT
            elif state == State.ABSTRACT:
                # Skip headings
                next(it)
                next(it)

                for l in langs:
                    result[l].abstract = next(it).children[0].text

                state = State.GENERIC
            elif state == State.GENERIC:
                if it.lookahead().type == "heading":
                    if it.lookahead().children[0].text.startswith("ignore"):
                        break
                    else:
                        state = State.HEADING
                else:
                    next(it)
            elif state == State.HEADING:
                for l in langs:
                    # Strangely, AttrDict converts the list to a tuple
                    result[l].sections.append(Section(next(it).children[0].text))

                state = State.NON_HEADING
            elif state == State.NON_HEADING:
                if it.lookahead().type == "heading":
                    state = State.GENERIC
                elif it.lookahead().type == "paragraph":
                    for l in langs:
                        result[l].sections[-1].parts.append(
                            TextNode(next(it).children[0].text)
                        )
                elif it.lookahead().type == "block_quote":
                    code_spec = next(it).children[0].children[0].text
                    if parts := FILE_INFO_REGEX.match(code_spec):
                        path, start, end = parts.groups()
                        path = source_path.parent / Path(path)
                        start = int(start)
                        end = int(end)

                        for l in langs:
                            result[l].sections[-1].parts.append(
                                CodeReference(path, start, end)
                            )
                    else:
                        raise RuntimeError(f"Wrong file spec: {code_spec}")
                elif it.lookahead().type == "newline":
                    next(it)
                    continue
                else:
                    pprint(next(it))
                    raise RuntimeError("Unhandled node type")

    except StopIteration:
        pass

    return result


PRAGMA_START_HERE = "-- doc:start-here"


def resolve_code(r: LangResult) -> LangResult:
    code_references = [
        p for s in r.sections for p in s.parts if isinstance(p, CodeReference)
    ]
    unique_files = list({r.file: None for r in code_references}.keys())
    file_lines = {f: f.read_text().splitlines() for f in unique_files}
    file_cur_line = {
        f: (
            1
            if not PRAGMA_START_HERE in file_lines[f]
            else file_lines[f].index(PRAGMA_START_HERE) + 1
        )
        for f in unique_files
    }

    new_sections = []
    for s in r.sections:
        new_parts = []
        for p in s.parts:
            if isinstance(p, CodeReference):
                prev = file_cur_line[p.file]
                start = p.start - 1
                end = p.end

                if prev < start:
                    missing_lines = file_lines[p.file][prev:start]
                    if not all(
                        l.strip().startswith("--") or len(l.strip()) == 0
                        for l in missing_lines
                    ):
                        missing_lines = list(
                            dropwhile(lambda s: len(s.strip()) == 0, missing_lines)
                        )
                        missing_lines.reverse()
                        missing_lines = list(
                            dropwhile(
                                lambda s: s.strip().startswith("--")
                                or len(s.strip()) == 0,
                                missing_lines,
                            )
                        )
                        missing_lines.reverse()
                        new_parts.append(
                            CodeBlock("\n".join(missing_lines), hidden=True)
                        )

                new_parts.append(
                    CodeBlock("\n".join(file_lines[p.file][start:end]), hidden=False)
                )

                file_cur_line[p.file] = end + 1
            else:
                new_parts.append(p)

        new_sections.append(dataclasses.replace(s, parts=new_parts))

    return dataclasses.replace(r, sections=new_sections)


def read_data(source_path: Path, langs: List[str]) -> Dict:
    first_result = first_pass(source_path, langs)
    return {k: resolve_code(v) for k, v in first_result.items()}
