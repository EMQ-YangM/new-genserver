{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_HADDOCK hide #-}

module Templates1
  ( mkElemIndexTypeFamily,
    mkApplyInstance,
    mkHandleCallInstance,
  )
where

import Data.Kind
import GHC.TypeLits
import Language.Haskell.TH hiding (Type)
import qualified Language.Haskell.TH as TH (Type)
import Unsafe.Coerce

mkElemIndexTypeFamily :: Integer -> DecsQ
mkElemIndexTypeFamily paramN = do
  -- Start by declaring some names.
  let [elemIndex, t, ts] = mkName <$> ["ElemIndex", "t", "ts"]
      -- Helper for building more readable type names rather than verbose gensyms
      mkT = pure . VarT . mkName . ('t' :) . show
      -- We want to make the kind signatures explicit here.
      binders =
        [ kindedTV t <$> [t|Type|],
          kindedTV ts <$> [t|[Type]|]
        ]
      -- This family ends up returning a Nat.
      resultKind = kindSig <$> [t|Nat|]
      -- We have to build n ElemIndex entries.
      equations = fmap buildEquation [0 .. pred paramN] ++ [errorCase]
      errorBody =
        [t|
          TypeError
            ( 'Text "'" ':<>: 'ShowType $(varT t)
                ':<>: 'Text "' is not a member of the type-level list"
                ':$$: 'ShowType $(varT ts)
            )
          |]
      -- The tySynEqn API changed in 2.15 so we need a guard here.
      -- buildEquation a single family instance equation; it uses lhsMatch
      -- to do so, making a type of the form 'ElemIndex n (n ': n0 : _)
      -- errorCase is invoked above to provide a readable error

      buildEquation n = tySynEqn Nothing (lhsMatch n) . litT . numTyLit $ n
      lhsMatch n = [t|$(conT elemIndex) $(mkT n) $(typeListT WildCardT <$> traverse mkT [0 .. n])|]
      errorCase = tySynEqn Nothing [t|$(conT elemIndex) $(varT t) $(varT ts)|] errorBody

  fmap pure =<< closedTypeFamilyD elemIndex
    <$> sequenceA binders
    <*> resultKind
    <*> pure Nothing
    <*> pure equations

mkApplyInstance :: Integer -> Dec
mkApplyInstance paramN =
  InstanceD
    Nothing
    (AppT constraint <$> typeParams)
    (AppT (AppT (ConT applyC) constraint) (typeListT PromotedNilT typeParams))
    [ FunD apply (zipWith mkClause [0 ..] typeParams),
      PragmaD (InlineP apply Inlinable FunLike AllPhases)
    ]
  where
    typeParams = VarT . mkName . ('f' :) . show <$> [0 .. pred paramN]
    [applyC, apply, f, r, union] = mkName <$> ["Apply", "apply", "f", "r", "Sum"]
    [constraint, a] = VarT . mkName <$> ["constraint", "a"]
    mkClause i nthType =
      Clause
        [VarP f, ConP union [LitP (IntegerL i), VarP r]]
        (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) nthType)))
        []

typeListT :: TH.Type -> [TH.Type] -> TH.Type
typeListT = foldr (AppT . AppT PromotedConsT)

mkHandleCallInstance :: Integer -> Dec
mkHandleCallInstance paramN =
  InstanceD
    Nothing
    [AppT (ConT functor) m]
    (AppT (AppT (ConT tHandleCall) (typeListT PromotedNilT typeParsms)) m)
    [ FunD handleCall (zipWith mkClause [0 ..] typeParsms1),
      PragmaD (InlineP handleCall Inlinable FunLike AllPhases)
    ]
  where
    [tSCall, tHandleCall, handleCall, union, tmap, fLine, hNil, functor, r, treq] =
      mkName <$> ["SCall", "HandleCall", "handleCall", "Sum", "<$>", ":|", "HNil", "Functor", "r", "Req"]
    [m] = VarT . mkName <$> ["m"]
    mkVar t i = VarT $ mkName $ t ++ show i
    mkNamet t i = mkName $ t ++ show i
    typeParsms =
      [ AppT (AppT (AppT (ConT tSCall) (mkVar "t" i)) (mkVar "req" i)) (mkVar "resp" i)
        | i <- [0 .. pred paramN]
      ]
    typeParsms1 =
      [ (mkNamet "f" i, mkVar "t" i, mkVar "req" i, mkVar "resp" i)
        | i <- [0 .. pred paramN]
      ]
    vars = VarP . mkName . ('f' :) . show <$> [0 .. pred paramN]
    fhlist = foldr (`InfixP` fLine) (ConP hNil []) vars
    mkClause i (iof, it, ireq, iresp) =
      Clause
        [fhlist, ConP union [LitP (IntegerL i), VarP r]]
        ( NormalB
            ( InfixE
                (Just (AppE (ConE union) (LitE (IntegerL i))))
                (VarE tmap)
                ( Just
                    ( AppE
                        (VarE iof)
                        ( SigE
                            (AppE (VarE 'unsafeCoerce) (VarE r))
                            (AppT (AppT (ConT treq) it) ireq)
                        )
                    )
                )
            )
        )
        []
