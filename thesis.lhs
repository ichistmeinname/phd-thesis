% **************************************************
% Document Class Definition
% **************************************************
\documentclass[%
    paper=A4,               % paper size --> A4 is default in Germany
    twoside=true,           % onesite or twoside printing
    openright,              % doublepage cleaning ends up right side
    parskip=false,           % spacing value / method for paragraphs
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

% Unicode chars not set up for the use with LaTeX
\DeclareUnicodeCharacter{251C}{\mbox{\kern.23em
  \vrule height2.4exdepth1exwidth.4pt\vrule height2.4ptdepth-1.8ptwidth.23em}}
\DeclareUnicodeCharacter{2500}{\mbox{\vrule height2.4ptdepth-1.8ptwidth.5em}}
\DeclareUnicodeCharacter{2502}{\mbox{\kern.23em \vrule height2.4exdepth1exwidth.4pt}}
\DeclareUnicodeCharacter{2514}{\mbox{\kern.23em \vrule height2.4exdepth-1.8ptwidth.4pt\vrule height2.4ptdepth-1.8ptwidth.23em}}


%include polycode.fmt
%include forall.fmt
%include greek.fmt

%format not = "not"
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

\newcommand{\hinl}[1]{\mintinline{Haskell}{#1}}
\newcommand{\cinl}[1]{\mintinline{Coq}{#1}}
        
\def\commentbegin{\quad\{\ }
\def\commentend{\}}

% Overwrite rule for parindent
\setlength{\parindent}{1em}
\setlength{\mathindent}{0.15cm}

\usemintedstyle[haskell]{automn}
\usemintedstyle[coq]{tango}

\newenvironment{excursus}[1]
{\vspace{0.5cm}
\hrule
\vspace{0.3cm}
\paragraph{Excursus: #1}}
{\vspace{0.3cm}
\hrule
\vspace{0.5cm}}



% **************************************************
% Document CONTENT
% **************************************************
\begin{document}

% --------------------------
% rename document parts
% --------------------------
%\renewcaptionname{ngerman}{\figurename}{Abb.}
%\renewcaptionname{ngerman}{\tablename}{Tab.}
%\renewcaptionname{english}{\figurename}{Fig.}
%\renewcaptionname{english}{\tablename}{Tab.}

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
\input{content/acknowledgement}
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
%\input{content/chapter/preliminaries}

\chapter{Generating Permutations via Non-deterministic Sorting}
\label{ch:permutations}
% %include content/chapter/Permutations/permutations.lcurry

\chapter{A Library for Probabilistic Functional Logic Programming}
\label{ch:pflp}
% %include content/chapter/pflp.lcurry

\chapter{Formal Reasoning About Effectful Non-Strict Programs}
\label{ch:reasoning} 
\input{content/chapter/FormalReasoning/FormalReasoning.tex}

%\chapter{Modelling Lazy Functional Logic Programming with Call-Time-Choice}
%\label{ch:modelling} 
%\input{content/chapter/free-curry}

\chapter{Conclusions}
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

% **************************************************
% End of Document CONTENT
% **************************************************
\end{document}
