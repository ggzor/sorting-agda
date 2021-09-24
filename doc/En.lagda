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

\title{\fontsize{14}{16.8}\selectfont Formal specification and verification of a sorting algorithm\vspace{-10pt}%
}
\author{\fontsize{10}{12}\selectfont Axel Suárez Polo$^1$, José de Jesús Lavalle Martínez$^1$\\
        $^1$Facultad de Ciencias de la Computación - BUAP}
\institute{}

\begin{document}

\maketitle

\thispagestyle{plain}

\begin{abstract}
\textit{\fontsize{10}{12}\selectfont This is the abstract in English.}
\end{abstract}

\section{Introduction}

{TODO}


\section{Specification}

{TODO}


\begin{code}
open import Data.Nat using (ℕ; suc; zero) public
open import Data.List using (List; _∷_; []) public
\end{code}

{TODO}


\begin{code}
n1 : ℕ
n1 = suc (suc zero)

n1' : ℕ
n1' = 2

list1 : List ℕ
list1 = 1 ∷ 2 ∷ 3 ∷ []
\end{code}

{TODO}


\begin{code}
open import Data.Nat using (_≤_) public
\end{code}

{TODO}


\begin{code}
open import Data.Nat using (z≤n; s≤s)

le1 : 0 ≤ 1
le1 = z≤n

le2 : 1 ≤ 2
le2 = s≤s z≤n
\end{code}

{TODO}


\begin{code}
open import Data.Unit using (⊤; tt) public
open import Data.Product using (_×_; _,_) public
\end{code}

\begin{code}
_≤*_ : (x : ℕ) → (l : List ℕ) → Set
x ≤* [] = ⊤
x ≤* (y ∷ l) = (x ≤ y) × (x ≤* l)
\end{code}

{TODO}


{TODO}


\begin{code}
ac1 : 1 ≤* (2 ∷ 3 ∷ [])
ac1 = s≤s z≤n , s≤s z≤n , tt

-- El tipo de ac1 normalizado
ac1' : 1 ≤ 2 × 1 ≤ 3 × ⊤
ac1' = s≤s z≤n , s≤s z≤n , tt
\end{code}

{TODO}


\begin{code}
sorted : (l : List ℕ) → Set
sorted [] = ⊤
sorted (x ∷ l) = x ≤* l × sorted l
\end{code}

{TODO}


{TODO}


\begin{code}
no-sort : List ℕ → List ℕ
no-sort l = []

no-sort-sorts : ∀ (l : List ℕ) → sorted (no-sort l)
no-sort-sorts l = tt
\end{code}

{TODO}


\begin{code}
data _~_ {A : Set} : List A → List A → Set where
  ~-nil    :                              [] ~ []
  ~-drop   : (x : A) { l l' : List A}  →  l ~ l' → (x ∷ l) ~ (x ∷ l')
  ~-swap   : (x y : A) (l : List A)    →  (x ∷ y ∷ l) ~ (y ∷ x ∷ l)
  ~-trans  : {l l' l'' : List A}       →  l ~ l' → l' ~ l'' → l ~ l''
\end{code}

{TODO}


{TODO}


\begin{code}
perm1 : (1 ∷ 2 ∷ 3 ∷ []) ~ (3 ∷ 1 ∷ 2 ∷ [])
perm1 =
  let p1 = ~-swap 1 3 (2 ∷ [])
      p2 = ~-drop 1 (~-swap 2 3 [])
   in ~-trans p2 p1
\end{code}

{TODO}


\begin{code}
Correct-Sorting-Algorithm : (f : List ℕ → List ℕ) → Set
Correct-Sorting-Algorithm f = ∀ (l : List ℕ) → sorted (f l) × l ~ f l
\end{code}

{TODO}


\section{Verification}

{TODO}


\begin{code}
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat.Properties using (≤-total)

insert : (x : ℕ) → (l : List ℕ) → List ℕ
insert x [] = x ∷ []
insert x (y ∷ l) with ≤-total x y
... | inj₁ x≤y = x ∷ y ∷ l
... | inj₂ y≤x = y ∷ insert x l

insertion-sort : List ℕ → List ℕ
insertion-sort [] = []
insertion-sort (x ∷ l) = insert x (insertion-sort l)
\end{code}

{TODO}


{TODO}


\begin{code}
≤*-insert : ∀ (x y : ℕ) (l : List ℕ) → x ≤ y → x ≤* l → x ≤* insert y l
≤*-insert x y [] x≤y x≤*l = x≤y , tt
≤*-insert x y (z ∷ l) x≤y (x≤z , z≤*l) with ≤-total y z
... | inj₁ y≤z = x≤y , x≤z , z≤*l
... | inj₂ z≤y = x≤z , (≤*-insert x y l x≤y z≤*l)
\end{code}

{TODO}


{TODO}


\begin{code}
open import Data.Nat.Properties using (≤-trans)

≤*-trans : {x y : ℕ} {l : List ℕ} → x ≤ y → y ≤* l → x ≤* l
≤*-trans {l = []} x≤y y≤*l = tt
≤*-trans {l = z ∷ l} x≤y (x≤z , y≤*l) =
  ≤-trans x≤y x≤z , ≤*-trans x≤y y≤*l
\end{code}

{TODO}


\begin{code}
insert-preserves-sorted :  ∀ (x : ℕ) (l : List ℕ)
                        →  sorted l
                        →  sorted (insert x l)
insert-preserves-sorted x [] sl = tt , tt
insert-preserves-sorted x (y ∷ l) (y≤*l , sl) with ≤-total x y
... | inj₁ x≤y = (x≤y , ≤*-trans x≤y y≤*l) , y≤*l , sl
... | inj₂ y≤x =
        ≤*-insert y x l y≤x y≤*l , insert-preserves-sorted x l sl
\end{code}

{TODO}


{TODO}


\begin{code}
insertion-sort-sorts : ∀ (l : List ℕ) → sorted (insertion-sort l)
insertion-sort-sorts [] = tt
insertion-sort-sorts (x ∷ l) =
  let  h-ind = insertion-sort-sorts l
   in  insert-preserves-sorted x (insertion-sort l) h-ind
\end{code}

{TODO}


\begin{code}
~-refl : {A : Set} {l : List A} → l ~ l
~-refl {l = []}     = ~-nil
~-refl {l = x ∷ l}  = ~-drop x ~-refl
\end{code}

{TODO}


\begin{code}
~-sym : {A : Set} {l l' : List A} → l ~ l' → l' ~ l
~-sym ~-nil                  = ~-nil
~-sym (~-drop x l~l')        = ~-drop x (~-sym l~l')
~-sym (~-swap x y l)         = ~-swap y x l
~-sym (~-trans l~l'' l''~l)  = ~-trans (~-sym l''~l) (~-sym l~l'')
\end{code}

{TODO}


\begin{code}
insert-~ : (x : ℕ) (l : List ℕ) → (x ∷ l) ~ (insert x l)
insert-~ x [] = ~-drop x ~-nil
insert-~ x (y ∷ l) with ≤-total x y
... | inj₁ x≤y = ~-refl
... | inj₂ y≤x = ~-trans (~-swap x y l) (~-drop y (insert-~ x l))
\end{code}

{TODO}


\begin{code}
~-insert : (x : ℕ) {l l' : List ℕ} → l ~ l' → insert x l ~ insert x l'
~-insert x {l} {l'} l~l' =
  let p1 = ~-sym (insert-~ x l)
      p2 = insert-~ x l'
      mid = ~-drop x l~l'
   in ~-trans p1 (~-trans mid p2)
\end{code}

{TODO}


\begin{code}
insertion-sort-~ : (l : List ℕ) → l ~ (insertion-sort l)
insertion-sort-~ [] = ~-nil
insertion-sort-~ (x ∷ l) =
  let h-ind = insertion-sort-~ l
      p1 = insert-~ x l
      p2 = ~-insert x h-ind
   in ~-trans p1 p2
\end{code}

{TODO}


{TODO}


\begin{code}
insertion-sort-correct : Correct-Sorting-Algorithm insertion-sort
insertion-sort-correct l =
  insertion-sort-sorts l , insertion-sort-~ l
\end{code}

\section{Acknowledgements}

{TODO}



\begin{thebibliography}{9}
\fontsize{10}{12}\selectfont
\bibitem{lamport94}
Leslie Lamport (1994) \emph{\LaTeX: a document preparation system}, Addison
Wesley, Massachusetts, 2nd ed.
\end{thebibliography}

\end{document}
