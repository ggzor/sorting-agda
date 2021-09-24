<!-- vim: set tw=80 spell spelllang=es,en_us: -->
# Especificación y verificación formal de un algoritmo de ordenamiento
# Formal specification and verification of a sorting algorithm

## Abstract
## Abstract

Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est Lorem ipsum dolor sit amet.

This is the abstract in English.

## Introducción
## Introduction

Crear software correcto es una de las tareas más complejas que se tiene en el
desarrollo de software debido a que requiere un entendimiento completo tanto del
problema que se desea resolver, como de la solución que se propone
\cite{lamport94}.
\par
Primeramente, se deben establecer los criterios para determinar que el software
desarrollado es correcto. La expresión de estos criterios debe realizarse de
forma no ambigua y completa; es decir, no debe estar sujeta a la interpretación
y debe abarcar todas las características deseadas del software en cuestión. Esto
se conoce como la \textbf{especificación} del software.
\par
Una vez que se ha hecho la especificación, el siguiente problema es asegurar que
la solución desarrollada satisface los criterios que se establecieron.
Nuevamente, no es una tarea fácil ya que los mecanismos utilizados para
asegurarse de la correspondencia con la especificación deben ser correctos por
si mismos y además debe revisarse que se hayan aplicado correctamente. Esto es
la \textbf{verificación} del software.
\par
En este documento se utiliza el lenguaje de programación \textbf{Agda}, que al
contar con \textit{tipos dependientes}, permite realizar la especificación,
implementación y verificación en el mismo lenguaje. Este lenguaje pertenece a la
clase de métodos formales conocida como \textit{demostración automática de teoremas}.

TODO

## Especificación de un algoritmo de ordenamiento
## Specification

Para empezar, tenemos que determinar a qué nos referimos cuando decimos que un
algoritmo es un \textbf{algoritmo de ordenamiento}.
\par
Para los fines de este documento, nos enfocaremos en el ordenamiento de listas
de números naturales, por lo que tenemos que importar las definiciones
correspondientes de la librería estándar de Agda.

TODO

> ../Sorting.agda:3-4

Esto nos permite construir valores de cada uno de los tipos correspondientes,
utilizando sus constructores.

TODO

> ../Ejemplos.agda:8-15

Para determinar el orden entre los elementos, utilizamos la relación menor o
igual de los naturales que nos proporciona la librería estándar:

TODO

> ../Sorting.agda:6-6

Esta relación, nos permite dar evidencia de que un natural es menor que otro,
construyendo términos de este tipo:

TODO

> ../Ejemplos.agda:18-24

Ahora podemos definir una relación auxiliar $\leq^\star$, en la que siendo $x$
un natural y $l$ una lista de naturales; $x \leq^\star l$ significa que $x$ es
menor que todos los elementos de $l$; en otras palabras, $x$ acota inferiormente
a $l$. Esta relación se puede definir inductivamente de la siguiente forma en
Agda:

TODO

> ../Sorting.agda:8-9

> ../Sorting.agda:12-14

Lo que la relación está codificando es lo siguiente:
\begin{itemize}
  \item Cualquier natural acota inferiormente una lista vacía.
  \item Un natural $x$ acota inferiormente una lista que inicia con $y$, si
        $x \leq y$ y $x$ acota inferiormente al resto de la lista.
\end{itemize}
\par
Nótese además que se está haciendo uso del tipo producto $\times$ y unit $\top$
que nos ofrece Agda en la librería estándar para expresar la noción de
tautología y de conjunción, correspondientemente.

TODO

Esta relación se puede utilizar para dar evidencia de que un número acota
inferiormente a una lista:

TODO

> ../Ejemplos.agda:27-32

Con la anterior relación, podemos definir un predicado para verificar que una
lista se encuentra ordenada, también de forma inductiva en Agda:

TODO

> ../Sorting.agda:16-18

Nuevamente, esta definición codifica lo siguiente:
\begin{itemize}
  \item Un lista vacía está ordenada.
  \item Una lista $x :: l$ está ordenada si $x$ es menor que todos los elementos
        de $l$ y además $l$ está ordenada.
\end{itemize}
\par

TODO

Podría parecer que esta es la única definición que necesitamos para especificar
que un algoritmo de ordenamiento es correcto, sin embargo, esto permite que
funciones como la siguiente, sean consideradas algoritmos de ordenamiento, ya
que al devolver la lista vacía, esta devolviendo efectivamente una lista
ordenada, pero no la lista ordenada que queremos:

TODO

> ../Ejemplos.agda:35-39

Por lo tanto, es necesario refinar la especificación. La otra condición que
necesitamos de un algoritmo de ordenamiento es que devuelva una lista con los
mismos elementos que la lista de entrada, aunque ordenados. Es decir,
necesitamos que el algoritmo de ordenamiento no borre, agregue o duplique
elementos arbitrarios de la lista de entrada.
\par
En otras palabras, lo que necesitamos del algoritmo de ordenamiento es que
devuelva una \textit{permutación} de la lista original, y que además esta
permutación se encuentre ordenada.
\par
Para esto, podemos definir la relación de permutación $\sim$ entre dos listas como
sigue en Agda:

TODO

> ../Sorting.agda:21-25

Esta definición codifica lo siguiente:
\begin{itemize}
  \item Una lista vacía es permutación de si misma.
  \item Si una lista $l'$ es permutación de otra lista $l$, agregar un elemento
        cualquiera $x$ al inicio de ambas, conserva la relación de permutación.
  \item Si a una lista $l$ se le agregan al inicio dos elementos $x$ y $y$, esta
        nueva lista es permutación de la lista $l$ con los elementos $x$ y $y$
        agregados en orden inverso.
  \item La relación de permutación es transitiva, es decir, dadas tres listas $l$,
        $l'$ y $l''$, si $l \sim l'$ y $l' \sim l''$, entonces $l \sim l''$.
\end{itemize}

TODO

Lo que nos permite dar evidencia de que una lista es permutación de otra:

TODO

> ../Ejemplos.agda:42-46

Con estas definiciones, finalmente podemos especificar de forma no ambigua y
completa lo que consideramos como algoritmo de ordenamiento:

TODO

> ../Sorting.agda:27-28

Esta predicado define un algoritmo de ordenamiento como una función que recibe
una lista de naturales y devuelve una lista de naturales; tal que para todas las
listas de naturales, aplicar esta función devuelve una lista ordenada y además
la lista que devuelve es permutación de la lista de entrada.

TODO

## Verificación
## Verification

Para llevar a cabo la verificación, primero necesitamos definir nuestra función
de ordenamiento. En este caso, verificaremos la siguiente implementación del
algoritmo de ordenamiento por inserción, utilizando su definición recursiva:

TODO

> ../InsertionSort.agda:3-14

Esta definición hace uso de la función {\tt $\leq$-total} que decide si un
natural es menor o igual que otro, o viceversa; devolviendo {\tt inj$_1$} en el
caso de que sea menor o igual e {\tt inj$_2$} en caso contrario. Estos
constructores pertenecen al \textit{tipo suma} definido en la librería estándar
de Agda.

TODO

Para poder verificar que la función de {\tt insertion-sort} cumple con la
especificación, requerimos probar primero propiedades e invariantes que siguen
las funciones definidas con anterioridad. Por ejemplo, una invariante que es
relevante es la siguiente:

TODO

> ../InsertionSort.agda:16-20

Lo que esta invariante nos dice es que si $x \leq y$ y además $x$ acota
inferiormente a $l$, entonces $x$ seguirá acotando inferiormente a la lista que
resulte de insertar $y$ en $l$.
\par
Para hacer la demostración, se procede por inducción sobre la lista $l$, que en
Agda se traduce en realizar un análisis de casos sobre el parámetro que
corresponde a la lista. Además, en el caso en el que $l$ sea una lista con al
menos un elemento $z$, se utiliza una cláusula {\tt with}, para permitir a Agda
continuar la normalización de la expresión {\tt insert y l}.
\par
Agda realiza normalización tan pronto como tiene un termino reducible, como
puede observarse en el caso de que la lista sea de la forma $z :: l$ y al
aparecer este valor en los tipos de los parámetros, puede proceder con la
reducción de $x \leq^\star l$, por lo que el argumento que
corresponde a la prueba de que $x\leq^\star l$, se normaliza a una pareja, tal y
como lo indica su definición; lo que nos permite realizar el análisis de casos
sobre ese argumento.

TODO

Una propiedad importante de la relación $\leq^\star$, es que es transitiva con
respecto a la relación $\leq$. Esto lo podemos demostrar como sigue, por
inducción sobre la lista acotada:

TODO

> ../Sorting.agda:31-36

Con esta propiedad, podemos realizar la prueba de la invariante más relevante:

TODO

> ../InsertionSort.agda:22-29

Esta demostración muestra que teniendo una lista ordenada $l$, al realizar {\tt
insert x l} para cualquier natural $x$, se preserva la propiedad de que la lista
está ordenada. Nuevamente, se procede por inducción sobre la lista de entrada y
se replica parcialmente la estructura de {\tt insert}, utilizando la cláusula
{\tt with} para permitir a Agda continuar con la normalización. Además se hace
uso de los lemas que se demostraron con anterioridad.

TODO

Finalmente, podemos probar que {\tt insertion-sort} devuelve una lista ordenada,
por inducción sobre la lista y utilizando el lema anterior, ya que la definición
de {\tt insertion-sort} utiliza repetidamente la función {\tt insert}.

TODO

> ../InsertionSort.agda:31-35

Para probar que la lista devuelta por {\tt insertion-sort} es una permutación de
la lista original, tenemos que probar algunos lemas adicionales. Por ejemplo,
que la relación de permutación es reflexiva para todas las listas, realizando la
prueba por inducción:

TODO

> ../Sorting.agda:39-41

Además, podemos probar que la relación de permutación es simétrica, por
inducción sobre el constructor de la permutación:

TODO

> ../Sorting.agda:43-47

Con esto, podemos probar que {\tt insert x l} devuelve una permutación de la
lista $x :: l$, con lo que garantizamos que insert no remueve o agrega elementos
a la lista salvo $x$:

TODO

> ../InsertionSort.agda:37-41

Lo que nos permite a su vez probar que insertar el mismo elemento en dos listas,
preserva la propiedad de permutación, haciendo uso de este lema y la
transitividad de $\sim$:

TODO

> ../InsertionSort.agda:43-48

Finalmente, podemos probar con estos dos lemas sobre la relación $\sim$ e {\tt
insert} que {\tt insertion-sort} devuelve efectivamente una permutación de la
lista original:

TODO

> ../InsertionSort.agda:50-56

Básicamente se realiza inducción sobre la lista y se utilizan directamente ambos
lemas sobre la lista original y la hipótesis de inducción.

TODO

Así tenemos los lemas necesarios para asegurar que {\tt insertion-sort} cumple
con la propiedad que establecimos en la especificación y el sistema de tipos de
Agda se encargará de la verificación de que nuestro razonamiento es correcto,
implicando que hemos verificado el algoritmo de ordenamiento.

TODO

> ../InsertionSort.agda:58-60

## Agradecimientos
## Acknowledgements

Este trabajo fue financiado por la Vicerrectoría de Investigación y Estudios de
Posgrado de la BUAP, en el marco del programa ``Haciendo ciencia en la BUAP
2021".

TODO
