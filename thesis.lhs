% **************************************************
% Document Class Definition
% **************************************************
\documentclass[%
    paper=A4,               % paper size --> A4 is default in Germany
    twoside=true,           % onesite or twoside printing
    openright,              % doublepage cleaning ends up right side
    parskip=false,          % spacing value / method for paragraphs
    chapterprefix=true,     % prefix for chapter marks
    10pt,                   % font size
    headings=normal,        % size of headings
    listof=totoc,           % include listof entries in toc
    titlepage=on,           % own page for each title page
    captions=tableabove,    % display table captions above the float env
    draft=false,            % value for draft version
]{scrbook}%

% **************************************************
% Setup YOUR thesis document in this file !
% **************************************************

\input{setup}
\newcommand{\coqrepl}{$\Pi$>}
\newcommand{\curryrepl}{$\mathbf{\vdash}$}
\newcommand{\haskellrepl}{$\lambda$>}
\newcommand{\func}{\textbackslash}

% Lhs2Tex-specifics
%include polycode.fmt
%include forall.fmt
%include greek.fmt

%format not = "not"
%format ?* = "\mathbin{?_1}"
%format ? = "\mathbin{?}"
%format ^ = "\mathbin{^}"
%format +++ = "\mathbin{+\!\!\!+\!\!\!+}"
%format >>>= = "\mathbin{>\!\!\!>\!\!\!>\mkern-6.7mu=}"
%format >>>=! = "\mathbin{>\!\!\!>\!\!\!>\mkern-6.7mu=!}"
%format Values a = "\{"a"\}"
%format frac x y = "\frac{"x"}{"y"}"
%format (frac x y) = "\frac{"x"}{"y"}"
%format repl = "\lambda\mkern-3mu"
%format replHS = "\lambda_{hs}\mkern-3mu"
%format =? = "\stackrel{?}{\equiv}"
%format tau1
%format tau2
%format tau3

\def\commentbegin{\quad\{\ }
\def\commentend{\}}
                
% **************************************************
% Document CONTENT
% **************************************************
\begin{document}

% --------------------------
% rename document parts
% --------------------------

\addto\extrasenglish{%
  \renewcommand{\chapterautorefname}{Chapter}
  \renewcommand{\sectionautorefname}{Section}
  \renewcommand{\subsectionautorefname}{Section}
  \renewcommand{\subsubsectionautorefname}{Section}
  \renewcommand{\paragraphautorefname}{Section}
  \renewcommand{\subparagraphautorefname}{Section}
}

% Overwrite rule for parindent
\setlength{\parindent}{1em}
\setlength{\mathindent}{0.15cm}

% --------------------------
% Front matter
% --------------------------
\pagenumbering{roman}			% roman page numbing (invisible for empty page style)
\pagestyle{empty}				% no header or footers
\input{content/frontpage}
\cleardoublepage

\pagestyle{plain}				% display just page numbers
\input{content/abstract}
\cleardoublepage
%
%\input{content/acknowledgement}
\cleardoublepage
%
\setcounter{tocdepth}{2}		% define depth of toc
\tableofcontents				% display table of contents
\cleardoublepage

% --------------------------
% Body matter
% --------------------------
\pagenumbering{arabic}			% arabic page numbering
\setcounter{page}{1}			% set page counter
\pagestyle{maincontentstyle} 	% fancy header and footer

\chapter{Introduction}
\label{ch:intro}
\input{content/chapter/introduction}
 
\chapter{Declarative Programming}
\label{ch:dp}
%include content/chapter/preliminaries.lhs
%include content/chapter/Preliminaries/Haskell.lhs
%include content/chapter/Preliminaries/Curry.lcurry
\input{content/chapter/Preliminaries/Coq.tex}
 
\chapter{Generating Permutations via Non\--deterministic Sorting}
\label{ch:permutations}
%include content/chapter/Permutations/permutations.lcurry

\chapter{Probabilistic Functional Logic Programming}
\label{ch:pflp}
%include content/chapter/pflp.lcurry
 
\chapter{Formal Reasoning About Effectful Non\--Strict Programs}
\label{ch:reasoning}
\input{content/chapter/FormalReasoning/FormalReasoning.tex}
 
\chapter{Conclusion}
\label{ch:conclusion}
\input{content/chapter/conclusion}

% --------------------------
% Back matter
% --------------------------
%
{%
\setstretch{1.1}
\renewcommand{\bibfont}{\normalfont\small}
\setlength{\biblabelsep}{0pt}
\setlength{\bibitemsep}{0.5\baselineskip plus 0.5\baselineskip}
\printbibliography
}
\cleardoublepage

\appendix\cleardoublepage
\input{content/appendix}

\input{content/statement}
        
% **************************************************
% End of Document CONTENT
% **************************************************
\end{document}
