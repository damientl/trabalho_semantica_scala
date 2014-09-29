/*
* To change this template, choose Tools | Templates
* and open the template in the editor.
*/

package interl2

abstract class Tipo{
def getT1:Tipo
def getT2:Tipo
}
case class Inteiro() extends Tipo{
def getT1:Tipo = null
def getT2:Tipo = null
}
case class Boleano() extends Tipo{
def getT1:Tipo = null
def getT2:Tipo = null
}
case class Unidade() extends Tipo {
def getT1:Tipo = null
def getT2:Tipo = null
}
case class Funcao(t1: Tipo, t2: Tipo) extends Tipo {
def getT1:Tipo = t1
def getT2:Tipo = t2
}
case class Refer(t: Tipo) extends Tipo {
def getT1:Tipo = null
def getT2:Tipo = null
}


abstract class Expr
case class N (n:Int) extends Expr
case class B (b:Boolean) extends Expr
case class Sum (e1: Expr, e2: Expr) extends Expr
//case class Prod (e1: Expr, e2: Expr) extends Expr
//case class Dif (e1: Expr, e2: Expr) extends Expr
case class Atr (s: String, e1: Expr) extends Expr
case class GreaterEq (e1: Expr, e2: Expr) extends Expr
case class If (e1: Expr, e2: Expr, e3: Expr) extends Expr
case class Asg (e1: Expr, e2: Expr) extends Expr
case class Var(s: String) extends Expr
case class Deref (s:String) extends Expr
case class Ref (e:Expr) extends Expr
case class Skip() extends Expr
case class Seq (e1: Expr, e2: Expr) extends Expr
case class W (e1: Expr, e2: Expr) extends Expr
case class Fn (s:String, t: Tipo, e: Expr) extends Expr
case class App (e1: Expr, e2: Expr) extends Expr
//case class X (s:String) extends Expr
case class Let (s:String, t: Tipo, e1: Expr, e2: Expr) extends Expr
case class LetRec (s: String, f: Tipo, e1: Expr, e2: Expr) extends Expr


class L2Interpreter {
// Verificador de Tipos
def typecheck(e:Expr, gamma: List[(String,Tipo)], delta: List[String]) : Option[Tipo] =
e match {
case N (_) => Some(Inteiro())
case B (_) => Some(Boleano())
case Sum (e1, e2) =>
(typecheck(e1,gamma, delta), typecheck(e2,gamma, delta)) match {
case (Some(Inteiro()), Some(Inteiro())) => Some(Inteiro())
case _ => None
}
case GreaterEq(e1, e2) =>
(typecheck(e1,gamma, delta), typecheck(e2,gamma, delta)) match {
case (Some(Inteiro()), Some(Inteiro())) => Some(Boleano())
case _ => None
}
case If (e1, e2, e3) =>
(typecheck(e1,gamma, delta))match {
case (Some(Boleano())) =>
val t2:Option[Tipo] = typecheck(e2,gamma, delta)
val t3:Option[Tipo] = typecheck(e3,gamma, delta)
if((t2 != None) && (t3 != None) && (t2 == t3)) {
t2
} else None
case _ => None
}
case Deref (s) =>
if(delta.contains(s)) {
Some(Inteiro())
} else None

case Atr (s, e1) =>
if(delta.contains(s)) {
val t:Option[Tipo] = typecheck(e1,gamma, delta)
if(t == Some(Inteiro())){
Some(Unidade())
}else None
} else None

case Skip () => Some(Unidade())

case Seq (e1, e2) =>
val t:Option[Tipo] = typecheck(e1,gamma, delta)
if(t == Some(Unidade())){
typecheck(e2,gamma, delta)
} else None

case W (e1, e2) =>
val t:Option[Tipo] = typecheck(e1,gamma, delta)
if(t == Some(Boleano())) {
//typecheck(e2,gamma, delta)
if(Some(Unidade()) == typecheck(e2,gamma, delta)) {
Some(Unidade())
} else None
}else None
case Fn (s, t, e) =>
var gammaaux = (s,t) :: gamma
val t2:Option[Tipo] = typecheck(e, gammaaux, delta)
if(t2 != None){
Some(Funcao(t, t2.get))
} else None

case App (e1, e2) =>
val tip1:Option[Tipo] = typecheck(e1, gamma, delta)
val tip2:Option[Tipo] = typecheck(e2, gamma, delta)
if(tip1 != None && tip2 != None){
val tipoE1:Tipo = tip1.get
val tipoE2:Tipo = tip2.get
tipoE1 match {
case Funcao(t1,t2) =>
if(tipoE1.getT1 == tipoE2){
Some(tipoE1.getT1)
}else None
case _ => None
}
}else None

case Var(s) =>
var i = 0
val variable = s
var lookUp = false
var aux:(String,Tipo) = gamma.apply(i)
while(i < gamma.length && !lookUp){
aux = gamma.apply(i)
if(variable == aux._1){
lookUp = true
}
i += 1
}
if(lookUp){
Some(aux._2)
}else None

case Let (s, t, e1, e2) =>
var gammaaux = (s,t)::gamma
if(Some(t) == typecheck(e1, gamma, delta)) {
typecheck(e2,gammaaux, delta)
}else None

case LetRec (s, f, e1, e2) =>
var gammaaux = (s,f)::gamma
if(f.getT1 != null && f.getT2 != null) {
e1 match {
case Fn(sf, tf ,ef) =>
gammaaux = (sf,tf)::gammaaux
if(Some(f.getT2) == typecheck(ef,gammaaux, delta)){
typecheck(e2, gammaaux, delta)
}else None
}
} else None



}
// Avaliacao
def isvalue(e:Expr) : Boolean = e match {
case N(_) => true
//case X(_) => true
case B(_) => true
case Fn(_,_,_) => true
case Skip() => true
case _ => false
}
type Endereco = String
type Memoria = List[(Endereco,Int)]

def step(e: Expr, sigma: Memoria): Option[(Expr, Memoria)] = e match {
case N(_) => None
case B(_) => None
case Sum (e1, e2) => (e1,e2) match{
case (N(n1),N(n2)) => Some ((N(n1 + n2), sigma))
case (e1, e2) => if (isvalue(e1)) {
step(e2,sigma) match {
case Some((e2lin, sigmalin)) =>
Some((Sum(e1,e2lin), sigmalin))
case None => None
}
} else {
step(e1, sigma) match {
case Some((e1lin, sigmalin)) =>
Some((Sum(e1lin, e2), sigmalin))
case None => None
}
}
}
case GreaterEq(e1, e2) => (e1,e2) match{
case (N(n1),N(n2)) =>
if(n1 >= n2) {
Some ((B(true), sigma))
}else Some ((B(false), sigma))


case (e1, e2) => if (isvalue(e1)) {
step(e2,sigma) match {
case Some((e2lin, sigmalin)) =>
Some((GreaterEq(e1,e2lin), sigmalin))
case None => None
}
} else {
step(e1, sigma) match {
case Some((e1lin, sigmalin)) =>
Some((GreaterEq(e1lin, e2), sigmalin))
case None => None
}
}
}
case If(e1, e2, e3) => (e1, e2, e3) match {
case (B(b), e2, e3) => if(b) {
step(e2, sigma)
} else step(e3 , sigma)
case (e1, e2, e3) => step(e1,sigma) match {
case Some((e1lin, sigmalin)) =>
Some((If(e1lin, e2, e3), sigmalin))
case None => None
}
}
case Seq (e1, e2) =>
if(isvalue(e1)) {
step(e2, sigma)
}else {
step(e1,sigma) match {
case Some((e1lin, sigmalin)) =>
Some((Seq(e1lin, e2), sigmalin))
case None => None
}
}
case Atr(s, e1) =>
(e1) match {
case N(n) =>
var i = 0
val variable = s
var sigmalin:List[(String,Int)] = List()
var aux = sigma.apply(i)
while(i < sigma.length){
aux = sigma.apply(i)
if(variable != aux._1){
sigmalin = aux :: sigmalin
}
i += 1
}
sigmalin = (s,n) :: sigmalin
Some(Skip(), sigmalin)

case (e1) =>
step(e1,sigma) match {
case Some((e1lin, sigmalin)) =>
Some((Atr(s, e1lin), sigmalin))
case None => None
}
}

case Deref (s) =>
var i = 0
var lookUp = false
var aux = sigma.apply(i)
var variable = s
while(i < sigma.length && !lookUp){
aux = sigma.apply(i)
if(variable == aux._1){
lookUp = true
}
i += 1
}
val t:Int = aux._2
Some(N(t), sigma)


// case Prod (e1, e2) => ...
// case Dif (e1, e2) => ...
// case Eq (e1, e2) => ...
//case If(B(true), e2, e3) => Some(e2, sigma)
//case If(B(false), e2, e3) => Some(e3, sigma)
// case If(e1, e3, e3) => ....
// .....
}
def eval(e: Expr, sigma:Memoria): Option[(Expr, Memoria)] =
step(e,sigma) match {
case None => Some((e,sigma))
case Some((elin, sigmalin)) => eval(elin, sigmalin)
}
}


object Main {

/**
* @param args the command line arguments
*/
def main(args: Array[String]): Unit = {

// Expressao e memoria para teste
//val ex:Expr = Sum(Sum(N(5),N(10)), Sum(N(10),N(100)))
//val ex:Expr = GreaterEq(N(3), N(5))
//val aux1:Expr = If(GreaterEq(N(1), N(5)), Sum(N(5),N(10)), Sum(N(10),N(100)) )
val ex:Expr = Atr("l2", Deref("l1"))
//val ex:Expr = Seq(aux2, aux1)

//val ex:Expr = Fn("x", Inteiro(), Sum(Sum(N(5),N(10)), Sum(N(10),N(100))))
//val ex:Expr = App(Fn("x", Inteiro(), Sum(Sum(N(5),N(10)), Sum(N(10),N(100)))), B(true))
//val ex:Expr = Var("z")
//val ex:Expr = Let("x", Funcao(Inteiro(), Inteiro()), Fn("y", Inteiro(), Sum(Var("y"), N(10))), App(Var("x"), N(10)))
/*val ex:Expr = LetRec("fat",
Funcao(Inteiro(), Inteiro()),
Fn("x", Inteiro(), If(GreaterEq(N(0), Var("x")), N(1), Sum(Var("x"), App(Var("fat"),N(2))))),
App(Var("fat"),N(5))
)*/
val sigma: List[(String,Int)] = List(("l1",5), ("l2",7))
var gamma: List[(String,Tipo)] = List()

val delta: List[String] = List("l1", "l2", "l3", "l4")
val interpretador = new L2Interpreter()
val tipo = interpretador.typecheck(ex,gamma,delta)
println()
println("Expressao L2: " + ex)
println()
println("Tipo: " + tipo)
if(tipo != None){
val res = interpretador.eval(ex,sigma)

res match {
case Some((exp_final, sigma_final)) =>
println("Resultado da avaliacao: " + exp_final)
println(sigma_final)
case _=> println("Erro na avaliaçao da expreçao")
}
}
}

}