
class Subclass<X> extends Super<X, List<X>>
-->
Subclass<X> <: Super<X, List<X>>

Integer <: Number

F(List<Number>) -> Bool
x: List<Integer>
F(x) type error

Invariance:
List<A> <: List<B> ?
Javas antwort: A  = B!

Covariance:
 A <: B
 ->
 T<A> <: T<B>

Contravariance:
 B <: A
 ->
 T<A> <: T<B>

Statt Covariance hat Java wildcards:

F(List<? extends Number>)
T <: Number
-->
List<T> <: List<? extends Number>

Statt Contravariance:
F<List<? super Integer>)
Integer <: T
-->
List<t> <: List<? super Integer>
