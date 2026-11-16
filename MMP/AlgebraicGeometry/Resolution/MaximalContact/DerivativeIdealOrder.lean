module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters

/-!
# Orders of derivative ideals

Let `X` be a smooth scheme of finite type over a field `k` of characteristic zero, all of whose
irreducible components have positive dimension, and `I ⊆ 𝒪_X` an ideal sheaf nonzero at the
generic point of every irreducible component. First, `I ⊆ D(I)`: near every point there are
local coordinates `x_1, …, x_n` with `n ≥ 1`, hence a derivation `∂` with `∂ x_1 = 1`, and every
`f ∈ I` is `∂(x_1 f) - x_1 ∂f`. Differentiating lowers the order by exactly one
until it reaches zero: at every point `x`, closed or not, `ord_x D(I) = max(ord_x I - 1, 0)`.
A derivation maps `𝔪_x^r` into `𝔪_x^(r-1)` by the Leibniz rule; conversely, for derivations `δ_i`
dual to a regular system of parameters `t_i` at `x`, the Euler identity
`∑ t_i δ_i(f) ≡ r f (mod 𝔪_x^(r+1))` for `f ∈ 𝔪_x^r`, with `r` a unit, produces a derivative of
order `r - 1`. The computation takes place in `𝒪_{X,x}`, a localization of a finitely presented
`k`-algebra, with which forming the derivative ideal commutes.

Two consequences follow. With `m = maxord I` finite, the maximal contact ideal
`MC(I) = D^(m-1)(I)` has order `max(ord_x I - m + 1, 0) = 0` where `ord_x I < m`, so it is the
unit ideal there. And if `K` satisfies `(D^i K)^μ ⊆ K^(μ-i)` for `i < μ`, with `μ ≥ 1`, a point
`x` with `ord_x K = r < μ` has `D^(μ-1)(K)_x ⊇ D^r(K)_x = 𝒪_{X,x}`, and `(D^(μ-1) K)^μ ⊆ K` forces
`K_x = 𝒪_{X,x}`; so every point of the cosupport of `K` has order at least `μ`.

## Main results

* `MMP.Resolution.le_derivativeIdeal`: `I ≤ derivativeIdeal sX I`.
* `MMP.Resolution.multAt_derivativeIdeal_eq_tsub_one`, `MMP.Resolution.multAt_derivativeIdeal`:
  `multAt (derivativeIdeal sX I) x = multAt I x - 1`.
* `MMP.Resolution.multAt_higherDerivativeIdeal`: `multAt (D^j I) x = multAt I x - j`.
* `MMP.Resolution.stalk_maximalContactIdeal_eq_top_of_multAt_lt`: if `multAt I x < maxOrder I`
  then the stalk of `maximalContactIdeal sX I` at `x` is `⊤`.
* `MMP.Resolution.support_eq_cosupport_of_higherDerivativeIdeal_pow_le`: under the balancing
  condition, `K.support` is the cosupport of the marked ideal `(K, μ)`.

## Implementation notes

Orders take values in `ℕ∞`, whose truncated subtraction gives `r - 1 = max(r - 1, 0)`.
Positive dimension of the components is needed: on `X = Spec k` every derivation vanishes, so
`D(⊤) = ⊥` has order `⊤` while `ord_x ⊤ - 1 = 0`. The order formulas need neither
quasi-compactness, nor equidimensionality, nor `I` nonzero at the generic points: the computation
is stalk-local, and the stated results keep these clauses of the source's standing setting. The
finiteness of `maxOrder I` is an explicit hypothesis; the bound `maxOrder I ≥ 1` is not, since it
follows from `multAt I x < maxOrder I`.
The cosupport of an ideal sheaf is `Scheme.IdealSheafData.support`; that of the marked ideal
`(K, μ)` is `MMP.Resolution.MarkedIdeal.cosupport`. The marking `μ` is fixed and need not be
`maxord K`, unlike in `MMP.Resolution.IsDBalanced`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.74(3), 3.79, after Def. 3.79 and
  after Def. 3.83]
-/

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace MMP.Resolution

section LocalAlgebra

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]

/-- A derivation maps `P^(n+1)` into `P^n` (Leibniz rule). -/
private theorem derivation_mem_pow {A₀ R : Type*} [CommRing A₀] [CommRing R] [Algebra A₀ R]
    (δ : Derivation A₀ R R) {P : Ideal R} :
    ∀ {n : ℕ} {f : R}, f ∈ P ^ (n + 1) → δ f ∈ P ^ n
  | 0, _, _ => by simp
  | n + 1, f, hf => by
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine add_mem (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ]
      exact mul_comm (δ a) b ▸ Ideal.mul_mem_mul (derivation_mem_pow δ ha) hb
    · rw [map_add]
      exact add_mem hx hy

/-- If `J ⊆ 𝔪^(n+1)` then `D(J) ⊆ 𝔪^n`. -/
private theorem derivativeIdealOfRing_le_pow {J : Ideal A} {n : ℕ}
    (h : J ≤ maximalIdeal A ^ (n + 1)) : derivativeIdealOfRing k J ≤ maximalIdeal A ^ n :=
  Ideal.span_le.mpr <| by
    rintro _ ⟨δ, f, hf, rfl⟩
    exact derivation_mem_pow δ (h hf)

private theorem idealOrder_eq_natCast_iff (J : Ideal A) (n : ℕ) :
    idealOrder J = n ↔ J ≤ maximalIdeal A ^ n ∧ ¬ J ≤ maximalIdeal A ^ (n + 1) := by
  rw [← natCast_le_idealOrder_iff', ← natCast_le_idealOrder_iff', not_le, Nat.cast_add,
    Nat.cast_one, ENat.lt_add_one_iff (ENat.coe_ne_top n)]
  exact ⟨fun h => ⟨h.ge, h.le⟩, fun h => le_antisymm h.2 h.1⟩

section Euler

variable {d : ℕ} (t : Fin d → A) (δ : Fin d → Derivation k A A)

/-- The Euler operator `E = ∑ tᵢ δᵢ`. -/
private def euler (g : A) : A := ∑ i, t i * δ i g

variable {t δ}
variable (ht : Ideal.span (Set.range t) = maximalIdeal A)
  (hδ : ∀ i j, δ i (t j) = if i = j then 1 else 0)

include ht

private theorem t_mem (i : Fin d) : t i ∈ maximalIdeal A :=
  ht ▸ Ideal.subset_span ⟨i, rfl⟩

omit ht in
private theorem euler_mul (a b : A) :
    euler t δ (a * b) = a * euler t δ b + b * euler t δ a := by
  simp only [euler, Derivation.leibniz, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem euler_mem (g : A) : euler t δ g ∈ maximalIdeal A :=
  Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (t_mem ht i)

include hδ in
private theorem euler_sub_mem_sq {b : A} (hb : b ∈ maximalIdeal A) :
    euler t δ b - b ∈ maximalIdeal A ^ 2 := by
  rw [← ht] at hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    have : euler t δ (t j) = t j := by
      simp [euler, hδ]
    simp [this]
  | zero => simp [euler]
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    simp only [euler, map_add, mul_add, Finset.sum_add_distrib]
    ring
  | smul c x hx' hx =>
    rw [smul_eq_mul, euler_mul,
      show c * euler t δ x + x * euler t δ c - c * x = c * (euler t δ x - x) + x * euler t δ c by
        ring]
    refine add_mem (Ideal.mul_mem_left _ _ hx) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul (ht ▸ hx') (euler_mem ht c)

include hδ in
/-- The Euler identity: `E(g) ≡ n g (mod 𝔪^(n+1))` for `g ∈ 𝔪^n`. -/
private theorem euler_sub_mem_pow :
    ∀ {n : ℕ} {g : A}, g ∈ maximalIdeal A ^ n → euler t δ g - n * g ∈ maximalIdeal A ^ (n + 1)
  | 0, g, _ => by simpa using euler_mem ht g
  | n + 1, g, hg => by
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [euler_mul,
        show a * euler t δ b + b * euler t δ a - ((n + 1 : ℕ) : A) * (a * b) =
          (euler t δ a - n * a) * b + a * (euler t δ b - b) by push_cast; ring]
      refine add_mem ?_ ?_
      · rw [pow_succ _ (n + 1)]
        exact Ideal.mul_mem_mul (euler_sub_mem_pow ha) hb
      · rw [show n + 1 + 1 = n + 2 by ring, pow_add]
        exact Ideal.mul_mem_mul ha (euler_sub_mem_sq ht hδ hb)
    · convert add_mem hx hy using 1
      simp only [euler, map_add, mul_add, Finset.sum_add_distrib]
      ring

include hδ in
/-- In characteristic `0`, if `g ∈ 𝔪^(n+1)` and every `δᵢ g ∈ 𝔪^(n+1)`, then `g ∈ 𝔪^(n+2)`:
the Euler operator gives `(n+1) g ≡ ∑ tᵢ δᵢ g ≡ 0 (mod 𝔪^(n+2))`. -/
private theorem mem_pow_add_two_of_derivation_mem [CharZero k] {n : ℕ} {g : A}
    (hg : g ∈ maximalIdeal A ^ (n + 1)) (hδg : ∀ i, δ i g ∈ maximalIdeal A ^ (n + 1)) :
    g ∈ maximalIdeal A ^ (n + 2) := by
  have hE : euler t δ g ∈ maximalIdeal A ^ (n + 2) := Ideal.sum_mem _ fun i _ =>
    pow_succ' (maximalIdeal A) (n + 1) ▸ Ideal.mul_mem_mul (t_mem ht i) (hδg i)
  have hu : IsUnit ((n + 1 : ℕ) : A) := by
    rw [← map_natCast (algebraMap k A)]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr n.succ_ne_zero)).map _
  refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
  simpa only [sub_sub_cancel] using sub_mem hE (euler_sub_mem_pow ht hδ hg)

include hδ in
/-- In a local `k`-algebra, `k` of characteristic `0`, with derivations dual to generators of
the maximal ideal, differentiating an ideal of finite order `r` gives order `r - 1`. -/
private theorem idealOrder_derivativeIdealOfRing [CharZero k] {J : Ideal A}
    (hJ : J ≤ derivativeIdealOfRing k J) {r : ℕ} (hr : idealOrder J = r) :
    idealOrder (derivativeIdealOfRing k J) = ((r - 1 : ℕ) : ℕ∞) := by
  rw [idealOrder_eq_natCast_iff] at hr ⊢
  obtain ⟨hr1, hr2⟩ := hr
  rcases r with _ | s
  · exact ⟨by simp, fun h => hr2 (hJ.trans (by simpa using h))⟩
  · exact ⟨derivativeIdealOfRing_le_pow hr1, fun hD => hr2 fun f hf =>
      mem_pow_add_two_of_derivation_mem ht hδ (hr1 hf)
        fun i => hD (Ideal.subset_span ⟨δ i, f, hf, rfl⟩)⟩

end Euler

end LocalAlgebra

section Geometry

open MMP.Flips.ResolutionInputs KaehlerDifferential

variable {k : Type*} [Field k] {X : Scheme} (sX : X ⟶ Spec (.of k))

/-- At any point of a smooth scheme over a field of characteristic `0`, the maximal ideal of the
local ring is generated by elements `t_j` admitting `k`-derivations `δ_i` with `δ_i t_j = δ_ij`. -/
private theorem exists_derivation_dual [CharZero k] [Smooth sX] (x : X) :
    letI := MMP.Mori.stalkAlgebra sX x
    ∃ (d : ℕ) (t : Fin d → X.presheaf.stalk x)
      (δ : Fin d → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)),
      Ideal.span (Set.range t) = maximalIdeal _ ∧ ∀ i j, δ i (t j) = if i = j then 1 else 0 := by
  classical
  let := MMP.Mori.stalkAlgebra sX x
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    (smooth_iff_forall_isRegularLocalRing_stalk sX).mp ‹_› x
  obtain ⟨d, t, ht⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
  obtain ⟨_, _, _⟩ := stalk_facts sX x
  have : Algebra.EssFiniteType k (ResidueField (X.presheaf.stalk x)) :=
    Algebra.EssFiniteType.of_surjective
      (IsScalarTower.toAlgHom k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)))
      residue_surjective
  have : Algebra.FormallySmooth k (ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallySmooth.of_perfectField
  obtain ⟨ht0, hli, -⟩ := cotangent_basis_of_regular t ht.1 ht.2
  have hli' := linearIndependent_tmul_D k t ht0 hli
  have : Module.Projective (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  have : Module.Flat (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := Module.Flat.of_projective
  obtain ⟨e, v, hvS, hvli, hvsp⟩ := exists_sumElim_basis _ hli' _ (span_tmul_range_D k)
  choose r hr using hvS
  have hu : (TensorProduct.mk (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))
      Ω[X.presheaf.stalk x⁄k] 1 ∘ fun i => KaehlerDifferential.D k (X.presheaf.stalk x)
        (Sum.elim t r i)) = Sum.elim (fun i => (1 : ResidueField (X.presheaf.stalk x)) ⊗ₜ
          KaehlerDifferential.D k (X.presheaf.stalk x) (t i)) v := by
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact hr j
  have hbij : Function.Bijective (Finsupp.linearCombination (X.presheaf.stalk x)
      (fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (Sum.elim t r i))) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [hu]
    refine ⟨hvli, ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp hvsp
  let b := basisOfBijective _ hbij
  refine ⟨d, t, fun i => (b.coord (Sum.inl i)).compDer (D k _), ht.1, fun i j => ?_⟩
  have hb : D k (X.presheaf.stalk x) (t j) = b (Sum.inl j) :=
    (basisOfBijective_apply _ hbij (Sum.inl j)).symm
  rw [Derivation.coe_comp, LinearMap.coe_comp, Function.comp_apply]
  erw [hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

end Geometry

/-- If an `A₀`-algebra `R` carries a derivation `δ` and an element `y` with `δ y = 1`, then every
ideal is contained in its first derivative: `f = δ (y f) - y δ f`. -/
private theorem le_derivativeIdealOfRing_of_derivation_eq_one {A₀ R : Type*} [CommRing A₀]
    [CommRing R] [Algebra A₀ R] (δ : Derivation A₀ R R) {y : R} (hy : δ y = 1) (J : Ideal R) :
    J ≤ derivativeIdealOfRing A₀ J := by
  intro f hf
  have hf' : f = δ (y * f) - y * δ f := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hy]
    ring
  rw [hf']
  exact sub_mem (Ideal.subset_span ⟨δ, y * f, J.mul_mem_left y hf, rfl⟩)
    (Ideal.mul_mem_left _ y (Ideal.subset_span ⟨δ, f, hf, rfl⟩))

/-- On a smooth scheme over a field all of whose irreducible components have positive dimension,
every ideal sheaf is contained in its first derivative. -/
@[mmp "lem_kr3d_ideal_subset_derivative_ideal"]
public theorem le_derivativeIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (I : X.IdealSheafData) : I ≤ derivativeIdeal sX I := by
  let ι := {W : X.affineOpens // letI := MMP.Mori.sectionAlgebra sX W.1
    ∃ (δ : Derivation k Γ(X, W) Γ(X, W)) (y : Γ(X, W)), δ y = 1}
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (ι := ι) (fun W ↦ W.1) ?_ ?_
  · refine eq_top_iff.mpr fun p _ ↦ ?_
    obtain ⟨U, hpU, n, x, hx, -, hn⟩ :=
      MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesOn sX p
    obtain ⟨Z, hZ, -, hZp⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X sX p
    have hn0 : 0 < n := by exact_mod_cast hn ▸ hZp ▸ hdim Z hZ
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hpW, hWU⟩ :=
      (X.isBasis_affineOpens).exists_subset_of_mem_open hpU U.2
    let W : X.affineOpens := ⟨W₀, hW₀⟩
    replace hWU : W.1 ≤ U := hWU
    letI := MMP.Mori.sectionAlgebra sX W.1
    obtain ⟨b, hb⟩ := hx W hWU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W,
      ⟨(b.coord ⟨0, hn0⟩).compDer (KaehlerDifferential.D k Γ(X, W)),
        restrictSection W hWU (x ⟨0, hn0⟩), by simp [← hb]⟩⟩, hpW⟩
  · rintro ⟨W, hW⟩
    letI := MMP.Mori.sectionAlgebra sX W.1
    obtain ⟨δ, y, hy⟩ := hW
    rw [derivativeIdeal_ideal]
    exact le_derivativeIdealOfRing_of_derivation_eq_one δ hy _

/-- On a scheme smooth over a field of characteristic zero all of whose irreducible components
have positive dimension, the order of the first derivative `derivativeIdeal sX I` at any point `x`
is `ord_x I - 1` (truncated at `0`). -/
public theorem multAt_derivativeIdeal_eq_tsub_one {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) (I : X.IdealSheafData)
    (x : X) : multAt (derivativeIdeal sX I) x = multAt I x - 1 := by
  classical
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.stalkAlgebra sX x
  let : Algebra Γ(X, W) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxW⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk x) :=
    MMP.Mori.isScalarTower_section_stalk sX W ⟨x, hxW⟩
  have : Algebra.FinitePresentation k Γ(X, W) :=
    Algebra.FinitePresentation.of_finiteType.mp (MMP.Mori.finiteType_sectionAlgebra sX hW)
  have hstalk : ∀ J : X.IdealSheafData, IdealSheafData.stalk J x =
      (J.ideal ⟨W, hW⟩).map (algebraMap Γ(X, W) (X.presheaf.stalk x)) := fun J =>
    IdealSheafData.stalk_eq_map_germ J x ⟨W, hW⟩ hxW
  have hD : IdealSheafData.stalk (derivativeIdeal sX I) x =
      derivativeIdealOfRing k (IdealSheafData.stalk I x) := by
    rw [hstalk, hstalk, derivativeIdeal_ideal, sectionDerivativeIdeal]
    exact derivativeIdealOfRing_map_localization (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl _
  have hle : IdealSheafData.stalk I x ≤ derivativeIdealOfRing k (IdealSheafData.stalk I x) :=
    hD ▸ stalk_le_stalk_of_le (le_derivativeIdeal sX hdim I) x
  unfold multAt
  rw [hD]
  generalize IdealSheafData.stalk I x = J at hle ⊢
  obtain ⟨d, t, δ, ht, hδ⟩ := exists_derivation_dual sX x
  cases h : idealOrder J with
  | top =>
    rw [ENat.top_sub_one]
    refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
    rw [natCast_le_idealOrder_iff']
    exact derivativeIdealOfRing_le_pow ((natCast_le_idealOrder_iff' _ _).mp (h ▸ le_top))
  | coe r =>
    rw [idealOrder_derivativeIdealOfRing ht hδ hle h]
    simp

/-- On a smooth equidimensional scheme of finite type over a field of characteristic zero all of
whose irreducible components have positive dimension, for an ideal sheaf nonzero at the generic
point of every irreducible component, the order of the first derivative `derivativeIdeal sX I`
at any point `x` is `ord_x I - 1` (truncated at `0`). -/
@[mmp "lem_kr3d_order_derivative_ideal"]
public theorem multAt_derivativeIdeal {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) {I : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) (x : X) :
    multAt (derivativeIdeal sX I) x = multAt I x - 1 :=
  multAt_derivativeIdeal_eq_tsub_one sX hdim I x

/-- On a smooth scheme all of whose components have positive dimension, the higher derivative
ideals of `I` increase with the order of differentiation. -/
private theorem monotone_higherDerivativeIdeal {k : Type*} [Field k] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) (I : X.IdealSheafData) :
    Monotone (higherDerivativeIdeal sX I) :=
  monotone_nat_of_le_succ fun n => by
    rw [higherDerivativeIdeal_succ]
    exact le_derivativeIdeal sX hdim _

/-- On a scheme smooth over a field of characteristic zero all of whose irreducible components
have positive dimension, differentiating `j` times lowers the order by `j`, truncated at zero. -/
public theorem multAt_higherDerivativeIdeal {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) (I : X.IdealSheafData)
    (j : ℕ) (x : X) : multAt (higherDerivativeIdeal sX I j) x = multAt I x - j := by
  induction j with
  | zero => simp [higherDerivativeIdeal_zero]
  | succ j ih =>
    rw [higherDerivativeIdeal_succ, multAt_derivativeIdeal_eq_tsub_one sX hdim, ih, tsub_tsub,
      Nat.cast_succ]

/-- An ideal of a local ring of order `0` is the unit ideal. -/
private lemma eq_top_of_idealOrder_eq_zero {R : Type*} [CommRing R] [IsLocalRing R]
    {J : Ideal R} (h : idealOrder J = 0) : J = ⊤ := by
  by_contra hJ
  simpa [h] using
    (natCast_le_idealOrder_iff' J 1).2 (by simpa using IsLocalRing.le_maximalIdeal hJ)

/-- If `a < m < ⊤` in `ℕ∞`, then `a - (m - 1) = 0`. -/
private lemma tsub_toNat_sub_one_eq_zero {a m : ℕ∞} (hm : m ≠ ⊤) (h : a < m) :
    a - ((m.toNat - 1 : ℕ) : ℕ∞) = 0 := by
  lift m to ℕ using hm
  lift a to ℕ using (h.trans (ENat.coe_lt_top m)).ne
  norm_cast at h ⊢
  simp only [ENat.toNat_coe]
  omega

/-- On a smooth, equidimensional scheme of finite type over a field of characteristic zero all of
whose irreducible components have positive dimension, for an ideal sheaf `I` nonzero at the
generic point of every irreducible component and of finite maximal order, the maximal contact
ideal `maximalContactIdeal sX I` has unit stalk at every point `x` where the order of `I` is
less than the maximal order. -/
@[mmp "lem_kr3d_maximal_contact_ideal_unit_below_max"]
public theorem stalk_maximalContactIdeal_eq_top_of_multAt_lt {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) {I : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) (hm : maxOrder I ≠ ⊤) {x : X}
    (hx : multAt I x < maxOrder I) :
    IdealSheafData.stalk (maximalContactIdeal sX I) x = ⊤ :=
  eq_top_of_idealOrder_eq_zero <|
    (multAt_higherDerivativeIdeal sX hdim I ((maxOrder I).toNat - 1) x).trans
      (tsub_toNat_sub_one_eq_zero hm hx)

/-- A point of the support of an ideal sheaf has multiplicity at least one. -/
private theorem one_le_multAt_of_mem_support {X : Scheme} {I : X.IdealSheafData} {x : X}
    (hx : x ∈ (I.support : Set X)) : 1 ≤ multAt I x := by
  have h1 : ((1 : ℕ) : ℕ∞) ≤ multAt I x := by
    rw [multAt, natCast_le_idealOrder_iff', pow_one]
    exact IsLocalRing.le_maximalIdeal fun ht =>
      (IdealSheafData.stalk_eq_top_iff_notMem_support I x).1 ht hx
  simpa using h1

/-- The balancing condition at `i = μ - 1` puts the cosupport of `K` inside the cosupport of
every `D^r K` with `r < μ`. -/
private theorem support_subset_support_higherDerivativeIdeal {k : Type*} [Field k] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) {μ : ℕ} (hμ : 1 ≤ μ)
    {K : X.IdealSheafData} (hK : higherDerivativeIdeal sX K (μ - 1) ^ μ ≤ K ^ (μ - (μ - 1)))
    {r : ℕ} (hr : r < μ) :
    (K.support : Set X) ⊆ (higherDerivativeIdeal sX K r).support := by
  intro x hx
  rw [Nat.sub_sub_self hμ, pow_one] at hK
  have h1 := Scheme.IdealSheafData.support_antitone hK hx
  rw [Scheme.IdealSheafData.support_pow _ _ (by omega)] at h1
  exact Scheme.IdealSheafData.support_antitone
    (monotone_higherDerivativeIdeal sX hdim K (by omega : r ≤ μ - 1)) h1

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- On a smooth variety of positive dimension over a field of characteristic zero, if an ideal
sheaf `K` satisfies `(D^i K)^μ ⊆ K^(μ-i)` for all `i < μ` (with `μ ≥ 1`), then every point of
the cosupport of `K` has order at least `μ`: `K.support` equals the cosupport of the marked
ideal `(K, μ)`. -/
@[mmp "lem_kr3e_balanced_order_dichotomy"]
public theorem support_eq_cosupport_of_higherDerivativeIdeal_pow_le {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hX : Mori.IsVariety k sX) (hdim : 1 ≤ topologicalKrullDim X) {μ : ℕ} (hμ : 1 ≤ μ)
    {K : X.IdealSheafData} (hK : ∀ i < μ, higherDerivativeIdeal sX K i ^ μ ≤ K ^ (μ - i)) :
    (K.support : Set X) = (⟨K, μ⟩ : MarkedIdeal X).cosupport := by
  haveI := hX.toIsIntegral
  have hcomp : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z := by
    simpa [irreducibleComponents_eq_singleton,
      (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq] using
      lt_of_lt_of_le (by exact_mod_cast zero_lt_one) hdim
  ext x
  refine ⟨fun hx => ?_,
    fun hx => mem_support_of_one_le_multAt K ((Nat.one_le_cast.2 hμ).trans hx)⟩
  change (μ : ℕ∞) ≤ multAt K x
  by_contra! hlt
  have hrx : multAt K x = (multAt K x).toNat := (ENat.coe_toNat hlt.ne_top).symm
  have hr := support_subset_support_higherDerivativeIdeal sX hcomp hμ (hK _ (by omega))
    (r := (multAt K x).toNat) (by exact_mod_cast hrx ▸ hlt) hx
  have h1 := one_le_multAt_of_mem_support hr
  rw [multAt_higherDerivativeIdeal sX hcomp, ← hrx, tsub_self] at h1
  exact absurd h1 (by decide)

end MMP.Resolution
