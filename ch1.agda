open import Data.Fin.Base using (Fin; fold; join)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _<_; _≤_; _+_)
open import Data.Rational.Unnormalised.Base as ℚ using (ℚᵘ; NonNegative; 1ℚᵘ; 0ℚᵘ; _+_; _*_; _-_; _÷_; _/_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)
open import Data.Integer.Base as ℤ using (ℤ; +_)
open import Data.Nat.Base as ℕ
open import Data.Sum.Base using (inj₁)
open import Data.Bool.Base
open import Data.Product
open import Relation.Nullary.Negation
open import Murray.Real as ℝ
open import Sqrt
open import Murray.RealProperties using (0≤∣x∣)



sum : {n : ℕ} → (Ω : Fin n) → (pr : ℕ → ℝ) → ℝ
sum {n} Ω pr = fold (λ x → ℝ) (λ {m} x → (pr m) ℝ.+ x) 0ℝ Ω

record finiteProbabilitySpace (n : ℕ) : Set where
    field
        Ω : Fin n
        pr : ℕ → ℝ
        pos : (m : ℕ) → ℝ.NonNegative (pr m)

record randomVar (n : ℕ) : Set where
    constructor _,_
    field
        fps : finiteProbabilitySpace n
        x : ℕ → ℝ

expectation : {n : ℕ} → (r : randomVar n) → ℝ
expectation r = fold (λ x → ℝ) 
                     (λ {m} x → ((finiteProbabilitySpace.pr (randomVar.fps r) m) ℝ.* 
                                 (randomVar.x r m) ℝ.+ x)) 
                     0ℝ 
                     (finiteProbabilitySpace.Ω (randomVar.fps r))

record event {n m : ℕ} {m ≤ n} : Set where
    field
        fps : finiteProbabilitySpace n
        subspace : Fin m

eventProb : (e : event) → ℝ
eventProb e = sum (event.subspace e) (finiteProbabilitySpace.pr (event.fps e)) 

variance : {n : ℕ} → (randomVar n) → ℝ
variance r  = ∣(expectation (randomVar.fps r ,  λ x → pow ((randomVar.x r x) ℝ.- (expectation r)) 2))∣

standard-deviation : {n : ℕ} → (randomVar n) → ℝ
standard-deviation r = sqrt (0≤∣x∣ (variance r))