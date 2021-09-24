from pathlib import Path
import sys

from jinja2 import Environment
from jinja2.loaders import FileSystemLoader

import md_parser

SOURCE_FILE = Path("./base.md")

env = Environment(
    loader=FileSystemLoader("."),
    variable_start_string=r"${",
    variable_end_string="}",
    trim_blocks=True,
    autoescape=False,
)
env.tests["of_type"] = md_parser.is_node_of_type

template = env.get_template("template.lagda")
langs = sys.argv[1:]

for target, data in md_parser.read_data(SOURCE_FILE, langs).items():
    Path(target).write_text(template.render(data=data), encoding="utf8")
