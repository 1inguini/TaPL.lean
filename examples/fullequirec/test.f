/* Examples for testing */

 "hello";

timesfloat 2.0 3.14159;

unit;

let x=true in x;


lambda f:Rec X.A->A. lambda x:A. f x;


lambda x:Bool. x;
(lambda x:Bool->Bool. if x false then true else false) 
  (lambda x:Bool. if x then false else true); 

lambda x:Nat. succ x;
(lambda x:Nat. succ (succ x)) (succ 0); 

{x=true, y=false}; 
{x=true, y=false}.x;
{true, false}; 
{true, false}.1; 


 
lambda x:<a:Bool,b:Bool>. x;



Counter = Rec P. {get:Nat, inc:Unit->P}; 

p = 
let create = 
  fix 
    (lambda cr: {x:Nat}->Counter.
      lambda s: {x:Nat}.
        {get = s.x,
         inc = lambda _:Unit. cr {x=succ(s.x)}})
in
  create {x=0};

p1 = p.inc unit;
p1.get;

get = lambda p:Counter. p.get;
inc = lambda p:Counter. p.inc;

Hungry = Rec A. Nat -> A;

f0 =
fix 
  (lambda f: Nat->Hungry.
   lambda n:Nat.
     f);

f1 = f0 0;
f2 = f1 2;

T = Nat;
  
fix_T = 
lambda f:T->T.
  (lambda x:(Rec A.A->T). f (x x))
  (lambda x:(Rec A.A->T). f (x x));

D = Rec X. X->X;

fix_D = 
lambda f:D->D.
  (lambda x:(Rec A.A->D). f (x x))
  (lambda x:(Rec A.A->D). f (x x));

diverge_D = lambda _:Unit. fix_D (lambda x:D. x);

lam = lambda f:D->D. f;
ap = lambda f:D. lambda a:D. f a;

myfix = lam (lambda f:D.
             ap (lam (lambda x:D. ap f (ap x x))) 
                (lam (lambda x:D. ap f (ap x x))));


 
NatList = Rec X. <nil:Unit, cons:{Nat,X}>; 

nil = <nil=unit> as NatList;

cons = lambda n:Nat. lambda l:NatList. <cons={n,l}> as NatList;

isnil = lambda l:NatList. 
case l of
<nil=u> ==> true
| <cons=p> ==> false;

hd = lambda l:NatList. 
case l of
<nil=u> ==> 0
| <cons=p> ==> p.1;

tl = lambda l:NatList. 
case l of
<nil=u> ==> l
| <cons=p> ==> p.2;

plus = fix (lambda p:Nat->Nat->Nat. 
lambda m:Nat. lambda n:Nat. 
if iszero m then n else succ (p (pred m) n));

sumlist = fix (lambda s:NatList->Nat. lambda l:NatList.
if isnil l then 0 else plus (hd l) (s (tl l)));

mylist = cons 2 (cons 3 (cons 5 nil));

sumlist mylist;



T = Nat->Nat;
lambda f:T. lambda x:Nat. f (f x);


lambda x:A. x;
