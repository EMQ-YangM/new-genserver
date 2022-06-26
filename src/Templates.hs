{-# LANGUAGE CPP, DataKinds, TemplateHaskell, QuasiQuotes, TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_HADDOCK hide #-}
module Templates 
 ( mkElemIndexTypeFamily
 , mkApplyInstance
 ) where

import Data.Kind
import Language.Haskell.TH hiding (Type)
import qualified Language.Haskell.TH as TH (Type)
import GHC.TypeLits
import Unsafe.Coerce

mkElemIndexTypeFamily :: Integer -> DecsQ
mkElemIndexTypeFamily paramN = do
  -- Start by declaring some names.
  let [elemIndex, t, ts] = mkName <$> ["ElemIndex", "t", "ts"]
      -- Helper for building more readable type names rather than verbose gensyms
      mkT = pure . VarT . mkName . ('t' :) . show
      -- We want to make the kind signatures explicit here.
      binders = [ kindedTV t  <$> [t| (Type -> Type) -> Type |]
                , kindedTV ts <$> [t| [(Type -> Type) -> Type] |] ]
      -- This family ends up returning a Nat.
      resultKind = kindSig <$> [t| Nat |]
      -- We have to build n ElemIndex entries.
      equations = fmap buildEquation [0..pred paramN] ++ [errorCase]
      errorBody = [t|
        TypeError ('Text "'" ':<>: 'ShowType $(varT t) ':<>:
                   'Text "' is not a member of the type-level list" ':$$:
                   'ShowType $(varT ts))
        |]
      -- The tySynEqn API changed in 2.15 so we need a guard here.
      -- buildEquation a single family instance equation; it uses lhsMatch
      -- to do so, making a type of the form 'ElemIndex n (n ': n0 : _)
      -- errorCase is invoked above to provide a readable error
#if MIN_VERSION_template_haskell(2,15,0)
      buildEquation n = tySynEqn Nothing (lhsMatch n) . litT . numTyLit $ n
      lhsMatch n = [t| $(conT elemIndex) $(mkT n) $(typeListT WildCardT <$> traverse mkT [0..n]) |]
      errorCase = tySynEqn Nothing [t| $(conT elemIndex) $(varT t) $(varT ts) |] errorBody
#else
      buildEquation n = tySynEqn (lhsMatch n) (litT . numTyLit $ n)
      lhsMatch n = [mkT n, typeListT WildCardT <$> traverse mkT [0..n] ]
      errorCase = tySynEqn [varT t, varT ts] errorBody
#endif

  fmap pure =<< closedTypeFamilyD elemIndex
    <$> sequenceA binders
    <*> resultKind
    <*> pure Nothing
    <*> pure equations

mkApplyInstance :: Integer -> Dec
mkApplyInstance paramN =
  InstanceD Nothing (AppT constraint <$> typeParams) (AppT (AppT (ConT applyC) constraint) (typeListT PromotedNilT typeParams))
    [ FunD apply (zipWith mkClause [0..] typeParams)
    , PragmaD (InlineP apply Inlinable FunLike AllPhases)
    ]
  where typeParams = VarT . mkName . ('f' :) . show <$> [0..pred paramN]
        [applyC, apply, f, r, union] = mkName <$> ["Apply", "apply", "f", "r", "Sum"]
        [constraint, a] = VarT . mkName <$> ["constraint", "a"]
        mkClause i nthType = Clause
#if MIN_VERSION_template_haskell(2,18,0)
          [ VarP f, ConP union [] [ LitP (IntegerL i), VarP r ] ]
#else
          [ VarP f, ConP union [ LitP (IntegerL i), VarP r ] ]
#endif
          (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT nthType a))))
          []


typeListT :: TH.Type -> [TH.Type] -> TH.Type
typeListT = foldr (AppT . AppT PromotedConsT)
