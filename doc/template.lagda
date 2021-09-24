\documentclass{llncs}
\usepackage{a4}
\usepackage{upgreek}
\usepackage{agda}
\usepackage{comment}

% Use fonts with a decent coverage of non-ASCII characters.
\usepackage{fontspec}

% Use special font families without TeX ligatures for Agda code. (This
% code is inspired by a comment by Enrico Gregorio/egreg:
% https://tex.stackexchange.com/a/103078.)
\newfontfamily{\AgdaSerifFont}{DejaVu Sans Mono}[Scale=MatchUppercase]
\newfontfamily{\AgdaSansSerifFont}{DejaVu Sans Mono}[Scale=MatchUppercase]
\newfontfamily{\AgdaTypewriterFont}{DejaVu Sans Mono}[Scale=MatchUppercase]
\renewcommand{\AgdaFontStyle}[1]{{\AgdaSansSerifFont{}#1}}
\renewcommand{\AgdaKeywordFontStyle}[1]{{\AgdaSansSerifFont{}#1}}
\renewcommand{\AgdaStringFontStyle}[1]{{\AgdaTypewriterFont{}#1}}
\renewcommand{\AgdaCommentFontStyle}[1]{{\AgdaTypewriterFont{}#1}}
\renewcommand{\AgdaBoundFontStyle}[1]{\textit{\AgdaSerifFont{}#1}}


\usepackage{lipsum}

\title{${data.title}}
\author{Axel Suárez Polo}
\institute
  {BUAP\\
   \email{axel.suarez@alumno.buap.mx}
  }

\begin{document}

\maketitle

\begin{abstract}
${data.abstract}
\end{abstract}

{% for section in data.sections %}
\section{${section.title}}
{% for part in section.parts %}
{% if part is of_type('TextNode') %}

${part.text}

{% elif part is of_type('CodeBlock') %}
{% if part.hidden %}
\iffalse
{% endif %}

\begin{code}
${part.text}
\end{code}
{% if part.hidden %}
\fi
{% endif %}
{% endif %}
{% endfor %}

{% endfor %}

\end{document}

