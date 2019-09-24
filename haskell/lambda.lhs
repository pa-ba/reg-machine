*** Haskell code for the lambda calculus example ***

--------------------------------------------------------------------------

Source language:

> data Expr = Val Int | Add Expr Expr | Var Int | Abs Expr | App Expr Expr
>             deriving Show

--------------------------------------------------------------------------

Functional semantics:

  data Value = Num Int | Fun (Value -> Value)
 
  type Env = [Value]

  eval :: Expr -> Env -> Value
  eval (Val n)   e = Num n
  eval (Add x y) e = case eval x e of
                        Num n -> case eval y e of
                           Num m -> Num (n+m)
  eval (Var i)   e = e !! i
  eval (Abs x)   e = Fun (\v -> eval x (v:e))
  eval (App x y) e = case eval x e of
                        Fun f -> f (eval y e)

--------------------------------------------------------------------------

Relational semantics:

> data Value = Num Int | Clo Expr Env
>              deriving Show
>
> type Env = [Value]
>
> eval :: Expr -> Env -> [Value]
> eval (Val n)   e = [Num n]
> eval (Add x y) e = [Num (n+m) | Num n <- eval x e, Num m <- eval y e]
> eval (Var i)   e = [e !! i]
> eval (Abs x)   e = [Clo x e]
> eval (App x y) e = [w | Clo x' e' <- eval x e, v <- eval y e, w <- eval x' (v:e')]

--------------------------------------------------------------------------

Target language:

> data Code = HALT | LOAD Int Code | LOOKUP Int Code
>           | STORE Reg Code | ADD Reg Code
>           | STC Reg Code | APP Reg Code
>           | ABS Code Code | RET
>           deriving Show

--------------------------------------------------------------------------

Compiler:

> compile :: Expr -> Code
> compile e = comp e first HALT
> 
> comp :: Expr -> Reg -> Code -> Code
> comp (Val n)   r c = LOAD n c
> comp (Var i)   r c = LOOKUP i c
> comp (Add x y) r c = comp x r (STORE r (comp y (next r) (ADD r c)))
> comp (App x y) r c = comp x r (STC r (comp y (next r) (APP r c)))
> comp (Abs x)   r c = ABS (comp x (next first) RET) c

--------------------------------------------------------------------------

Machine model:

> type Mem = Reg -> Val
>
> type Reg = Int
>
> data Val = VAL Int | CLO Code Env'
>            deriving Show
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
> next  :: Reg -> Reg
> next r = r+1

--------------------------------------------------------------------------

Virtual machine:

> type Conf = (Acc,Env',Lam,Mem)
>
> type Acc  = Value'
>
> type Env' = [Value']
>
> data Value' = Num' Int | Clo' Code Env'
>               deriving Show
>
> type Lam  = [Mem]
>
> exec :: Code -> Conf -> Conf
> exec HALT         (a,e,l,m)          = (a,e,l,m)
> exec (LOAD n c)   (a,e,l,m)          = exec c (Num' n,e,l,m)
> exec (LOOKUP i c) (a,e,l,m)          = exec c (e !! i,e,l,m)
> exec (STORE r c)  (Num' n,e,l,m)     = exec c (Num' n,e,l,set r (VAL n) m)
> exec (ADD r c)    (Num' a,e,l,m)     = exec c (Num' (n+a),e,l,m)
>                                        where VAL n = get r m
> exec (STC r c)    (Clo' c' e',e,l,m) = exec c (Clo' c' e',e,l,set r (CLO c' e') m)
> exec (APP r c)    (a,e,l,m)          = exec c' (a,a:e',m:l,set first (CLO c e) empty)
>                                        where CLO c' e' = get r m
> exec (ABS c' c)   (a,e,l,m)          = exec c (Clo' c' e,e,l,m)
> exec RET          (a,e',m:l,m')      = exec c (a,e,l,m)
>                                        where CLO c e = get first m'

--------------------------------------------------------------------------

Conversion functions:

> conv :: Value -> Value'
> conv (Num n)   = Num' n
> conv (Clo x e) = Clo' (comp x (next first) RET) (convE e)
> 
> convE :: Env -> Env'
> convE e = map conv e

--------------------------------------------------------------------------

Testing:

> nine :: Expr 
> nine = Add (Val 2) (Add (Val 3) (Val 4))
> 
> nine' :: Expr 
> nine' = Add (Add (Val 2) (Val 3)) (Val 4)
> 
> inc :: Expr
> inc = Abs (Add (Var 0) (Val 1))
> 
> three :: Expr
> three = App inc (Val 2)
>
> test :: Expr -> Acc
> test e = case exec (compile e) (Num' 0,[],[],empty) of
>             (a,_,_,_) -> a

--------------------------------------------------------------------------
