\documentclass[12pt]{llncs}
\usepackage{a4}
\usepackage{upgreek}
\usepackage{agda}
\usepackage{comment}
\usepackage{abstract}
\usepackage{sectsty}

\pagestyle{plain}

\usepackage[margin=2.5cm]{geometry}
\setlength{\parindent}{0pt}

\setlength{\absleftindent}{2cm}
\setlength{\absrightindent}{2cm}

\sectionfont{\fontsize{12}{14.4}\selectfont}

\renewcommand{\absnamepos}{flushleft}
\renewcommand{\abstractname}{\fontsize{12}{14.4}\selectfont Resumen}
\renewcommand{\refname}{\fontsize{12}{14.4}\selectfont Referencias}

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

\title{\fontsize{14}{16.8}\selectfont ${data.title}\vspace{-10pt}%
}
\author{\fontsize{10}{12}\selectfont Axel Suárez Polo$^1$, José de Jesús Lavalle Martínez$^1$\\
        $^1$Facultad de Ciencias de la Computación - BUAP}
\institute{}

\begin{document}

\maketitle

\thispagestyle{plain}

\begin{abstract}
\textit{\fontsize{10}{12}\selectfont ${data.abstract}}
\end{abstract}

{% for section in data.sections %}
\section{${section.title}}
{% for part in section.parts %}
{% if part is of_type('TextNode') %}

{${part.text}}

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

\begin{thebibliography}{9}
\fontsize{10}{12}\selectfont
\bibitem{lamport94}
Leslie Lamport (1994) \emph{\LaTeX: a document preparation system}, Addison
Wesley, Massachusetts, 2nd ed.
\end{thebibliography}

\end{document}

