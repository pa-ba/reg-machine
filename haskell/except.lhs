*** Haskell code for the exceptions example ***

Note: renamed 'fail' to 'myfail' to avoid clashing with prelude

--------------------------------------------------------------------------

Source language:

> data Expr = Val Int | Add Expr Expr | Throw | Catch Expr Expr
>             deriving Show

--------------------------------------------------------------------------

Semantics:

> eval :: Expr -> Maybe Int
> eval (Val n)     = Just n
> eval (Add x y)   = case eval x of
>                       Just n -> case eval y of
>                          Just m   -> Just (n + m)
>                          Nothing  -> Nothing
>                       Nothing -> Nothing
> eval Throw       = Nothing
> eval (Catch x y) = case eval x of
>                       Just n   -> Just n
>                       Nothing  -> eval y

--------------------------------------------------------------------------

Target language:

> data Code = HALT | LOAD Int Code | STORE Reg Code | ADD Reg Code |
>             THROW | MARK Reg Code Code | UNMARK Code
>             deriving Show

--------------------------------------------------------------------------

Compiler:

> compile :: Expr -> Code
> compile e = comp e first HALT

> comp :: Expr -> Reg -> Code -> Code
> comp (Val n)     r c = LOAD n c
> comp (Add x y)   r c = comp x r (STORE r (comp y (next r) (ADD r c)))
> comp (Throw)     r c = THROW
> comp (Catch x y) r c = MARK r (comp y r c) (comp x (next r) (UNMARK c))

--------------------------------------------------------------------------

Machine model:

> type Mem = Reg -> Val
>
> type Reg = Int
> 
> data Val = VAL {val :: Int} | HAN {han :: Han}
> 
> empty :: Mem
> empty = \n -> VAL 0
> 
> set :: Reg -> Val -> Mem -> Mem
> set r v m = \r' -> if r == r' then v else get r' m
> 
> get :: Reg -> Mem -> Val
> get r m = m r
> 
> first :: Reg
> first = 0
> 
> next :: Reg -> Reg
> next r = r+1

--------------------------------------------------------------------------

Virtual machine:

> type Conf = (Acc,Han,Mem)
>
> type Acc = Int
>
> type Han = (Code,Reg)
>
> exec :: Code -> Conf -> Conf
> exec HALT          (a,h,m)     = (a,h,m)
> exec (LOAD n c)    (a,h,m)     = exec c (n,h,m)
> exec (STORE r c)   (a,h,m)     = exec c (a,h, set r (VAL a) m)
> exec (ADD r c)     (a,h,m)     = exec c (val (get r m) + a,h, m)
> exec (THROW)       (a,h,m)     = myfail h m
> exec (MARK r c' c) (a,h,m)     = exec c (a,(c',r),set r (HAN h) m)
> exec (UNMARK c)    (a,(_,r),m) = exec c (a, han (get r m), m)
> 
> myfail :: Han -> Mem -> Conf
> myfail (c,r) m = exec c (0, han (get r m), m)

--------------------------------------------------------------------------

Testing:

> nine :: Expr
> nine = Add (Add (Val 2) (Val 3)) (Val 4)
> 
> nine' :: Expr
> nine' = Add (Val 2) (Add (Val 3) (Val 4))
>
> ok :: Expr
> ok = Catch (Add (Val 1) Throw) (Val 2)
> 
> crash :: Expr
> crash = Catch (Add Throw (Val 1)) Throw
> 
> test :: Expr -> Acc
> test e = case exec (compile e) (0,(HALT,0),empty) of
>             (a,_,_) -> a

--------------------------------------------------------------------------
