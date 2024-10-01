open import Murray.Real as ℝ
open import Murray.RealProperties
open import Data.Bool.Base
open import Data.Product


square : ℝ → ℝ
square i = i * i

-- given a real, provides a positive square root and a proof that it is a square root
postulate sqrt-constructive : {i : ℝ} → (NonNegative i) → Σ[ j ∈ ℝ ] (square j ≃ i) × NonNegative j

-- given a real, provides its square root
sqrt : {i : ℝ} → NonNegative i → ℝ
sqrt p = proj₁ (sqrt-constructive p)

postulate sqrt-preserves-ineq : {i j : ℝ} → (p1 : NonNegative i) → (p2 : NonNegative j) → (i ℝ.≤ j) → (sqrt p1 ℝ.≤ sqrt p2)

lem-square-preserves-ineqₗ : {i j : ℝ} → (p1 : NonNegative i) → (p2 : NonNegative j) → (i ℝ.≤ j) → (square i ℝ.≤ (i * j))
lem-square-preserves-ineqₗ p1 p2 ineq = *-mono-≤ p1 p1 (≤-reflexive (≃-refl)) ineq

lem-square-preserves-ineqᵣ : {i j : ℝ} → (p1 : NonNegative i) → (p2 : NonNegative j) → (i ℝ.≤ j) → ((i * j) ℝ.≤ square j)
lem-square-preserves-ineqᵣ p1 p2 ineq = *-mono-≤ p1 p2 ineq (≤-reflexive (≃-refl))

square-preserves-ineq : {i j : ℝ} → (p1 : NonNegative i) → (p2 : NonNegative j) → (i ℝ.≤ j) → (square i ℝ.≤ square j)
square-preserves-ineq p1 p2 ineq = ≤-trans (lem-square-preserves-ineqₗ p1 p2 ineq) (lem-square-preserves-ineqᵣ p1 p2 ineq)

-- lem-sqrt-preserves-ineq' : {i j : ℝ} → (p1 : Positive i) → (p2 : Positive j) → (square i ℝ.≤ square j) → (i * 1ℝ ℝ.≤ j * 1ℝ)
-- lem-sqrt-preserves-ineq' {i} {j} p1 p2 ineq = *-mono-≤ {!   !} {!   !} {!   !} {!   !}

-- sqrt-preserves-ineq' : {i j : ℝ} → (p1 : Positive i) → (p2 : Positive j) → (square i ℝ.≤ square j) → (i ℝ.≤ j)
-- sqrt-preserves-ineq' {i} {j} p1 p2 ineq = {!   !}