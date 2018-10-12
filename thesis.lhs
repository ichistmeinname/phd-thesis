% **************************************************
% Document Class Definition
% **************************************************
\documentclass[%
    paper=A4,               % paper size --> A4 is default in Germany
    twoside=true,           % onesite or twoside printing
    openright,              % doublepage cleaning ends up right side
    parskip=false,           % spacing value / method for paragraphs
    chapterprefix=true,     % prefix for chapter marks
    11pt,                   % font size
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

%include polycode.fmt
%include forall.fmt
%include greek.fmt

%format not = "not"
%format >>>= = "\mathbin{>\!\!\!>\!\!\!>\mkern-6.7mu=}"
%format >>>=! = "\mathbin{>\!\!\!>\!\!\!>\mkern-6.7mu=!}"
%format Values a = "\{"a"\}"
%format frac x y = "\frac{"x"}{"y"}"
%format (frac x y) = "\frac{"x"}{"y"}"
%format repl = "\lambda\mkern-3mu"
%format =? = "\stackrel{?}{\equiv}"
%format tau1
%format tau2
%format tau3

\def\commentbegin{\quad\{\ }
\def\commentend{\}}

% Overwrite rule for parindent
\setlength{\parindent}{1em}
\setlength{\mathindent}{0.15cm}

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

\chapter{A Library for Probabilistic Functional Logic Programming}
\label{ch:pflp}
%include content/chapter/pflp.lcurry

\chapter{Formal Reasoning About Effectful Programs with Non-Strictness}
\label{ch:reasoning} 
%\input{content/chapter/free-proving}

\chapter{Modelling Lazy Functional Logic Programming with Call-Time-Choice}
\label{ch:modelling} 
%\input{content/chapter/free-curry}

\chapter{Conclusions}
\label{ch:conclusion}
\input{content/chapter/conclusion}

% --------------------------
% Back matter
% --------------------------
\appendix\cleardoublepage
\input{content/appendix}
%
{%
\setstretch{1.1}
\renewcommand{\bibfont}{\normalfont\small}
\setlength{\biblabelsep}{0pt}
\setlength{\bibitemsep}{0.5\baselineskip plus 0.5\baselineskip}
\printbibliography[nottype=online]
\printbibliography[heading=subbibliography,title={Webpages}]
}
\cleardoublepage

\listoffigures
\cleardoublepage

\listoftables
\cleardoublepage

% **************************************************
% End of Document CONTENT
% **************************************************
\end{document}
