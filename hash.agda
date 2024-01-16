open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Data.Bool
open import Data.List

data Ident : Set where
  num : Nat -> Ident
  name : String -> Ident

data Stage : Set where
  ct rt : Stage

mutual
  data Ctx : Set where
    ∅ : Ctx
    _,_ : ∀ {s} (Γ : Ctx) -> Ty Γ s -> Ctx

  data Ty : Ctx -> Stage -> Set where
    weaken : ∀ {Γ s₁ s₂} {T : Ty Γ s₂} -> Ty Γ s₁ -> Ty (Γ , T) s₁
    Type : ∀ {Γ s} -> Ty Γ s
    El : ∀ {Γ s} -> Term {Γ} {s} Type pure -> Ty Γ s

  data Effect : Ctx -> Stage -> Set where
    impure : ∀ {Γ s} -> Effect Γ s
    read : ∀ {Γ s} -> Var Γ s -> Effect Γ s
    write : ∀ {Γ s} -> Var Γ s -> Effect Γ s

  Effects : Ctx -> Stage -> Set
  Effects Γ s = Effect Γ s -> Bool

  pure : ∀ {Γ s} -> Effects Γ s
  pure _ = false

  ⦅_⦆ : ∀ {Γ s} -> Effect Γ s -> Effects Γ s
  ⦅_⦆ = {!   !} -- need decision procedure for equality of effects

  _⊕_ : ∀ {Γ s} -> Effects Γ s -> Effects Γ s -> Effects Γ s
  e₁ ⊕ e₂ = λ eff -> e₁ eff ∨ e₂ eff

  _⊝_ : ∀ {Γ s} -> Effects Γ s -> Effects Γ s -> Effects Γ s
  e₁ ⊝ e₂ = λ eff -> if e₂ eff then false else e₁ eff

  data Term : {Γ : Ctx} {s : Stage} -> Ty Γ s -> Effects Γ s -> Set where


  data Var : Ctx -> Stage -> Set where
    Z : ∀ {Γ s} {T : Ty Γ s} -> Var (Γ , T) s
    S : ∀ {Γ s₁ s₂} {T : Ty Γ s₂} -> Var Γ s₁ -> Var (Γ , T) s₁

lookup-var : ∀ {Γ s} -> Var Γ s -> Ty Γ s
lookup-var {Γ = (_ , T)} Z = weaken T
lookup-var {Γ = (Γ , T)} {s} (S i) = weaken (lookup-var i)

