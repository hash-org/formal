open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Bool using (_∨_; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Data.Vec using (Vec; _∷_; [])

data Ident : Set where
  num : Nat -> Ident
  name : String -> Ident

data Stage : Set where
  ct rt : Stage

data ParamMod : Set where
  infer this : ParamMod

mutual

  data Ctx : Set

  data Var : Ctx -> Stage -> Set

  data Ty : Ctx -> Stage -> Set

  data Eff : Ctx -> Stage -> Set

  Effs : Ctx -> Stage -> Set
  Effs Γ s = Eff Γ s -> Bool

  data Term : {Γ : Ctx} {s : Stage} -> Ty Γ s -> Effs Γ s -> Set

  data Params : Ctx -> Stage -> Set

  data Args : {Γ : Ctx} {s : Stage} -> Params Γ s -> Effs Γ s -> Set

  data Ctx where
    ∅ : Ctx
    _,_ : ∀ {s} (Γ : Ctx) -> Ty Γ s -> Ctx

  weaken-effs : ∀ {Γ : Ctx} {s : Stage} {T : Ty Γ s} -> Effs Γ s -> Eff (Γ , T) s
  weaken-effs e = λ eff -> e (weaken eff)

  data Var where
    Z : ∀ {Γ s} {T : Ty Γ s} -> Var (Γ , T) s
    S : ∀ {Γ s₁ s₂} {T : Ty Γ s₂} -> Var Γ s₁ -> Var (Γ , T) s₁

  data Ty where
    weaken : ∀ {Γ s₁ s₂} {T : Ty Γ s₂} -> Ty Γ s₁ -> Ty (Γ , T) s₁

    Type : ∀ {Γ s} -> Ty Γ s
    ⟪_⟫ : ∀ {Γ s} -> Term {Γ} {s} Type pure -> Ty Γ s

    Effect : ∀ {Γ s} -> Ty Γ s

  data Eff where
    impure : ∀ {Γ s} -> Eff Γ s
    read : ∀ {Γ s} -> Var Γ s -> Eff Γ s
    write : ∀ {Γ s} -> Var Γ s -> Eff Γ s

    ⟪_⟫ : ∀ {Γ s} -> Term {Γ} {s} Effect pure -> Eff Γ s

  pure : ∀ {Γ s} -> Effs Γ s
  pure _ = false

  ⦅_⦆ : ∀ {Γ s} -> Eff Γ s -> Effs Γ s
  ⦅_⦆ = {!   !} -- need decision procedure for equality of effects

  _⊕_ : ∀ {Γ s} -> Effs Γ s -> Effs Γ s -> Effs Γ s
  e₁ ⊕ e₂ = λ eff -> e₁ eff ∨ e₂ eff

  _⊝_ : ∀ {Γ s} -> Effs Γ s -> Effs Γ s -> Effs Γ s
  e₁ ⊝ e₂ = λ eff -> if e₂ eff then false else e₁ eff

  data Term where

  ParamMods : Set
  ParamMods = ParamMod -> Bool

  enter : {Γ : Ctx} {s : Stage} -> Params Γ s -> Ctx

  data Params where
    ∅ : {Γ : Ctx} {s : Stage} -> Params Γ s
    _,_/_∈_ : {Γ : Ctx} {s : Stage} -> (Δ : Params Γ s) -> ParamMods -> Ident -> Ty (enter Δ) s -> Params Γ s

  enter {Γ} ∅ = Γ
  enter {Γ} (Δ , M / x ∈ T) = ((enter Δ) , T)

  len : {Γ : Ctx} {s : Stage} -> Params Γ s -> Nat
  len ∅ = 0
  len (Δ , M / x ∈ T) = suc (len Δ)

  names : {Γ : Ctx} {s : Stage} -> (Δ : Params Γ s) -> Vec Ident (len Δ)
  names ∅ = []
  names (Δ , M / x ∈ T) = x ∷ names Δ

  data Args where
    ∅ : {Γ : Ctx} {s : Stage} {e : Effs Γ s} -> Args ∅ e
    _,_/_≔_ : {Γ : Ctx} {s : Stage} {Δ : Params Γ s} {e₁ : Effs Γ s} {e₂ : Effs (enter Δ) s} {T : Ty (enter Δ) s} -> (δ : Args Δ e₁) -> (M : ParamMods) -> (x : Ident) -> Term T e₂ -> Args (Δ , M / x ∈ T) ((weaken e₁) ⊕ e₂)

lookup-var : ∀ {Γ s} -> Var Γ s -> Ty Γ s
lookup-var {Γ = (_ , T)} Z = weaken T
lookup-var {Γ = (Γ , T)} {s} (S i) = weaken (lookup-var i)

