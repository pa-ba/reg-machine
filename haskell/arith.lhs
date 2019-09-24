*** Haskell code for the arithmetic expressions example ***

--------------------------------------------------------------------------

Source language:

> data Expr = Val Int | Add Expr Expr 
>             deriving Show

--------------------------------------------------------------------------

Semantics:

> eval ::  Expr -> Int
> eval (Val n)   = n
> eval (Add x y) = eval x + eval y

--------------------------------------------------------------------------

Target language:

> data Code = LOAD Int Code | STORE Reg Code | ADD Reg Code | HALT
>             deriving Show

--------------------------------------------------------------------------

Compiler:

> compile :: Expr -> Code
> compile e = comp e first HALT
>  
> comp :: Expr -> Reg -> Code -> Code
> comp (Val n)   r c = LOAD n c
> comp (Add x y) r c = comp x r (STORE r (comp y (next r) (ADD r c)))

--------------------------------------------------------------------------

Machine model:

> type Mem = Reg -> Int
> 
> type Reg = Int
> 
> empty :: Mem
> empty = \n -> 0
> 
> set :: Reg -> Int -> Mem -> Mem
> set r n m = \r' -> if r == r' then n else get r' m
> 
> get :: Reg -> Mem -> Int
> get r m = m r
> 
> first :: Reg
> first = 0
> 
> next :: Reg -> Reg
> next r = r+1

--------------------------------------------------------------------------

Virtual machine:

> type Conf = (Acc,Mem)
>
> type Acc = Int
>
> exec :: Code -> Conf -> Conf
> exec (LOAD n c)  (a,m) = exec c (n,m)
> exec (STORE r c) (a,m) = exec c (a, set r a m)
> exec (ADD r c)   (a,m) = exec c (get r m + a, m)
> exec HALT        (a,m) = (a,m)

--------------------------------------------------------------------------

Testing:

> nine :: Expr
> nine = Add (Add (Val 2) (Val 3)) (Val 4)
>
> nine' :: Expr
> nine' = Add (Val 2) (Add (Val 3) (Val 4))
>
> test :: Expr -> Acc
> test e = fst $ exec (compile e) (0,empty)

--------------------------------------------------------------------------
