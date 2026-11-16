module

public import MMP.AlgebraicGeometry.Resolution.OrderAlongExceptional
public import MMP.AlgebraicGeometry.Resolution.OrderRestriction

/-!
# The maximal order under controlled transforms, and marked versus unmarked sequences

Let `X` be a smooth scheme over a field `k`, `Z ⊆ X` a smooth closed subscheme every irreducible
component of which has codimension `≥ 1`, and `I ⊆ 𝒪_X` an ideal sheaf nonzero at the generic
point of every irreducible component of `X`. If `ord_Z I = maxord I`, then the controlled
transform `π⁻¹_{Z*}I` along the blow-up `π : B_ZX → X` satisfies `maxord π⁻¹_{Z*}I ≤ maxord I`
(Kollár, Lemma 3.61).

The proof bounds the order at every point `q` of `B_ZX`. Off the exceptional divisor `π` is an
isomorphism and the transform is the pull-back. Over a point `p` of the centre, choose
coordinates `x_1, …, x_n` near `p` with `Z = V(x_1, …, x_r)` and a chart `U_ℓ` containing `q`. An
element `g` of `I_p` of order `m = maxord I` lies in `I_{Z,p}^m`, so up to a unit it is a form
`P(x_1, …, x_r)` of degree `m` with coefficients not all vanishing at `p`; on `U_ℓ` it is
`x_ℓ^m · h` with `h` the dehomogenization of `P`, a section of the transform. Mapping the chart
ring to `κ[T_i : i ≠ ℓ]`, `κ` the fraction field of `𝒪_X(U)/𝔭_p`, sends `h` to a nonzero
polynomial of degree `≤ m`, whose order at every point is `≤ m`; as this map is local at `q`,
the order of `h` at `q` is `≤ m`.

As a consequence, for a triple `(X, I, E)` with `m = maxord I`, a blow-up sequence is a smooth
blow-up sequence of order `≥ m` starting with the marked triple `(X, I, m, E)` if and only if it
is a smooth blow-up sequence of order `m` starting with `(X, I, E)`, and along such a sequence
the iterated marked transform of `(I, m)` and the iterated controlled transform of `I` are the
same ideal (Kollár, Remark 3.67): when `ord_Z I = m` all multiplicities in the controlled
transform equal `m`, so it is the ideal of the birational transform of `(I, m)`.

## Main results

* `MMP.Resolution.maxOrder_controlledTransform_le`
* `MMP.Resolution.ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq`

## Implementation notes

Smoothness is Mathlib's `AlgebraicGeometry.Smooth` of the structure morphism `X → Spec k` and of
`Z → X → Spec k`; it makes `X` locally noetherian, so every ideal sheaf is coherent. The
structure morphism is quasi-compact, the source's finite-type convention: it makes `Z` have
finitely many irreducible components, so that the exceptional divisor of the controlled
transform is a finite product.

The ideals `I_i` along a sequence are not data here: `IsOrderGeMarkedTripleSeq` computes them as
iterated marked transforms and `IsOrderMTripleSeq` as iterated controlled transforms. That the
two sequences carry the same ideals is therefore stated as a second conclusion: the last ideals
agree for every sequence of order `m`, hence (applied to its initial segments) all of them do.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Lemma 3.61, Remark 3.67]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing MMP.Flips.ResolutionInputs

universe u

namespace MMP.Resolution

/-- A local homomorphism does not decrease the order of an element. -/
private theorem mult_le_mult_map {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (ρ : R →+* S) (hρ : ∀ a ∈ maximalIdeal R, ρ a ∈ maximalIdeal S) (a : R) :
    mult a ≤ mult (ρ a) := by
  unfold mult idealOrder
  refine iSup₂_le fun j hj => le_iSup₂_of_le
    (f := fun (j : ℕ) (_ : Ideal.span {ρ a} ≤ maximalIdeal S ^ j) => (j : ℕ∞)) j ?_ le_rfl
  rw [Ideal.span_singleton_le_iff_mem] at hj ⊢
  have : Ideal.map ρ (maximalIdeal R ^ j) ≤ maximalIdeal S ^ j := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hρ) j
  exact this (Ideal.mem_map_of_mem _ hj)

/-- A bijective ring homomorphism of local rings does not increase the order of an ideal. -/
private theorem idealOrder_map_le {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (φ : R →+* S) (hφ : Function.Bijective φ) (K : Ideal R) :
    idealOrder (K.map φ) ≤ idealOrder K := by
  unfold idealOrder
  refine iSup₂_le fun j hj => le_iSup₂_of_le
    (f := fun (j : ℕ) (_ : K ≤ maximalIdeal R ^ j) => (j : ℕ∞)) j ?_ le_rfl
  rw [← IsLocalRing.map_maximalIdeal_of_surjective φ hφ.2, ← Ideal.map_pow] at hj
  rw [← Ideal.comap_map_of_bijective φ hφ (I := maximalIdeal R ^ j)]
  exact Ideal.map_le_iff_le_comap.1 hj

section Chart

open MvPolynomial

/-- The dehomogenization of a form of degree `m` has total degree at most `m`. -/
private theorem totalDegree_dehomogenize_le {σ R : Type*} [DecidableEq σ] [CommRing R]
    (ℓ : σ) {P : MvPolynomial σ R} {m : ℕ} (hP : P.IsHomogeneous m) :
    (dehomogenize R ℓ P).totalDegree ≤ m := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  have hdeg : ∑ i ∈ d.support, d i = m := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using hP (mem_support_iff.mp hd)
  rw [dehomogenize, aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add, ← hdeg]
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  have : (if h : i = ℓ then (1 : MvPolynomial {i : σ // i ≠ ℓ} R) else X ⟨i, h⟩).totalDegree
      ≤ 1 := by
    split_ifs
    · simp
    · exact (totalDegree_monomial_le _ _).trans (by simp)
  simpa using Nat.mul_le_mul_left (d i) this

/-- A prime `Q'` of `R[T_σ]` whose constants are exactly the prime `𝔭` of `R` is the contraction
of a prime of `κ[T_σ]`, `κ = Frac(R/𝔭)`. -/
private theorem exists_isPrime_comap_map_fractionRing_eq {σ R : Type*} [CommRing R]
    (𝔭 : Ideal R) [𝔭.IsPrime] (Q' : Ideal (MvPolynomial σ R)) [Q'.IsPrime]
    (hCQ : ∀ a, C a ∈ Q' ↔ a ∈ 𝔭) :
    ∃ Q2 : Ideal (MvPolynomial σ (FractionRing (R ⧸ 𝔭))), Q2.IsPrime ∧
      Q2.comap (map ((algebraMap (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭))).comp
        (Ideal.Quotient.mk 𝔭))) = Q' := by
  classical
  let Rb := R ⧸ 𝔭
  let K := FractionRing Rb
  let : Algebra (MvPolynomial σ Rb) (MvPolynomial σ K) := MvPolynomial.algebraMvPolynomial
  let mk1 : MvPolynomial σ R →+* MvPolynomial σ Rb := map (Ideal.Quotient.mk 𝔭)
  have hsurj1 : Function.Surjective mk1 := map_surjective _ Ideal.Quotient.mk_surjective
  have hker1 : RingHom.ker mk1 ≤ Q' := by
    rw [ker_map, Ideal.mk_ker, Ideal.map_le_iff_le_comap]
    exact fun a ha => (hCQ a).2 ha
  set Q1 := Q'.map mk1 with hQ1def
  have hQ1 : Q1.IsPrime := Ideal.map_isPrime_of_surjective hsurj1 hker1
  have hQ1c : Q1.comap mk1 = Q' := by
    rw [hQ1def, Ideal.comap_map_of_surjective' _ hsurj1, sup_eq_left.2 hker1]
  let M1 := Submonoid.map (C : Rb →+* MvPolynomial σ Rb) (nonZeroDivisors Rb)
  have : IsLocalization M1 (MvPolynomial σ K) :=
    MvPolynomial.isLocalization (nonZeroDivisors Rb) K
  have hdisj : Disjoint (M1 : Set (MvPolynomial σ Rb)) (Q1 : Set (MvPolynomial σ Rb)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ haQ
    obtain ⟨a0, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h2 : C a0 ∈ Q' := by
      rw [← hQ1c, Ideal.mem_comap]
      simpa [mk1] using haQ
    have h3 : Ideal.Quotient.mk 𝔭 a0 = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ((hCQ a0).1 h2)
    rw [h3] at ha
    exact zero_notMem_nonZeroDivisors ha
  refine ⟨Q1.map (algebraMap (MvPolynomial σ Rb) (MvPolynomial σ K)),
    IsLocalization.isPrime_of_isPrime_disjoint M1 _ Q1 hQ1 hdisj, ?_⟩
  ext t
  have ht : map ((algebraMap Rb K).comp (Ideal.Quotient.mk 𝔭)) t =
      algebraMap (MvPolynomial σ Rb) (MvPolynomial σ K) (mk1 t) := by
    simp only [mk1, MvPolynomial.algebraMap_def, map_map]
  have hQ2c : (Q1.map (algebraMap (MvPolynomial σ Rb) (MvPolynomial σ K))).comap
      (algebraMap (MvPolynomial σ Rb) (MvPolynomial σ K)) = Q1 :=
    IsLocalization.under_map_of_isPrime_disjoint M1 _ hQ1 hdisj
  rw [Ideal.mem_comap, ht, ← Ideal.mem_comap, hQ2c, ← Ideal.mem_comap, hQ1c]

/-- A ring map `θ : A → B` and a prime `𝔮` of `B` contracting to the prime `𝔔` of `A` induce a
local homomorphism `A_𝔔 → B_𝔮`, which does not decrease orders. -/
private theorem mult_algebraMap_le_mult_localization_of_comap {A B S : Type*} [CommRing A]
    [CommRing B] [CommRing S] [IsLocalRing S] [Algebra A S] (𝔔 : Ideal A) [𝔔.IsPrime]
    [IsLocalization.AtPrime S 𝔔] (θ : A →+* B) (𝔮 : Ideal B) [𝔮.IsPrime]
    (hθQ : ∀ s, θ s ∈ 𝔮 ↔ s ∈ 𝔔) (a : A) :
    mult (algebraMap A S a) ≤ mult (algebraMap B (Localization.AtPrime 𝔮) (θ a)) := by
  let Lq := Localization.AtPrime 𝔮
  let g : A →+* Lq := (algebraMap _ Lq).comp θ
  have hg : ∀ y : 𝔔.primeCompl, IsUnit (g y) := fun y =>
    IsLocalization.map_units Lq (⟨θ y, fun h => y.2 ((hθQ y).1 h)⟩ : 𝔮.primeCompl)
  let ρ : S →+* Lq := IsLocalization.lift (M := 𝔔.primeCompl) hg
  have hρ : ∀ s, ρ (algebraMap A S s) = algebraMap _ Lq (θ s) := fun s =>
    IsLocalization.lift_eq hg s
  have hρm : ∀ y ∈ maximalIdeal S, ρ y ∈ maximalIdeal Lq := by
    intro y hy
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl y
    have hspec := IsLocalization.mk'_spec S a s
    have ha : a ∈ 𝔔 := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔔 a, ← hspec]
      exact Ideal.mul_mem_right _ _ hy
    have hu : IsUnit (ρ (algebraMap A S (s : A))) := by
      rw [hρ]
      exact hg s
    rw [← Ideal.mul_unit_mem_iff_mem _ hu, ← map_mul, hspec, hρ]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Lq 𝔮 _).2 ((hθQ a).2 ha)
  exact (mult_le_mult_map ρ hρm _).trans (by rw [hρ])

/-- **The order of a polynomial in the chart ring along the fibre.** Let
`pres : R[T_σ] → A` be surjective with kernel inside `𝔭[T_σ]`, `𝔔` a prime of `A` lying over
the prime `𝔭` of `R`, and `S` the localization of `A` at `𝔔`. If `Q ∈ R[T_σ]` has total degree
`≤ d` and a coefficient outside `𝔭`, then the image of `Q` in `S` has order `≤ d`. -/
private theorem mult_algebraMap_pres_le {σ R A S : Type*} [Finite σ]
    [CommRing R] [CommRing A] [CommRing S] [IsLocalRing S] [Algebra A S]
    (pres : MvPolynomial σ R →+* A) (hsurj : Function.Surjective pres)
    (𝔭 : Ideal R) [𝔭.IsPrime] (hker : RingHom.ker pres ≤ Ideal.map C 𝔭)
    (𝔔 : Ideal A) [𝔔.IsPrime] [IsLocalization.AtPrime S 𝔔]
    (hC : ∀ a, pres (C a) ∈ 𝔔 ↔ a ∈ 𝔭)
    (Q : MvPolynomial σ R) (hQ : Q ∉ Ideal.map C 𝔭) {d : ℕ} (hd : Q.totalDegree ≤ d) :
    mult (algebraMap A S (pres Q)) ≤ d := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  set Q' := 𝔔.comap pres with hQ'
  have : Q'.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨Q2, hQ2, hQ2c⟩ := exists_isPrime_comap_map_fractionRing_eq 𝔭 Q' hC
  let Rb := R ⧸ 𝔭
  let K := FractionRing Rb
  let N := Fintype.card σ
  let e : σ ≃ Fin N := Fintype.equivFin σ
  let 𝔮 : Ideal (MvPolynomial (Fin N) K) := Q2.comap (rename e.symm)
  have h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  let α : R →+* K := (algebraMap Rb K).comp (Ideal.Quotient.mk 𝔭)
  let θ0 : MvPolynomial σ R →+* MvPolynomial (Fin N) K :=
    (rename e).toRingHom.comp (map α)
  have hθ0Q : ∀ t, θ0 t ∈ 𝔮 ↔ t ∈ Q' := by
    intro t
    change rename e.symm (rename e (map α t)) ∈ Q2 ↔ _
    rw [rename_rename, Equiv.symm_comp_self, rename_id, AlgHom.id_apply, ← hQ2c]
    exact Iff.rfl
  have hkerθ : RingHom.ker pres ≤ RingHom.ker θ0 := by
    refine hker.trans ?_
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [θ0, α, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  let θ : A →+* MvPolynomial (Fin N) K := RingHom.liftOfSurjective pres hsurj ⟨θ0, hkerθ⟩
  have hθ : ∀ t, θ (pres t) = θ0 t := fun t =>
    RingHom.liftOfSurjective_comp_apply pres hsurj ⟨θ0, hkerθ⟩ t
  have hθQ : ∀ s, θ s ∈ 𝔮 ↔ s ∈ 𝔔 := by
    intro s
    obtain ⟨t, rfl⟩ := hsurj s
    rw [hθ, hθ0Q, hQ', Ideal.mem_comap]
  refine (mult_algebraMap_le_mult_localization_of_comap 𝔔 θ 𝔮 hθQ _).trans ?_
  rw [hθ]
  have hne : θ0 Q ≠ 0 := by
    intro h0
    apply hQ
    rw [mem_map_C_iff]
    intro m
    have h1 : map α Q = 0 := (rename_injective e e.injective) (by simpa [θ0] using h0)
    have h2 : α (Q.coeff m) = 0 := by
      rw [← coeff_map, h1, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    have h3 : Ideal.Quotient.mk 𝔭 (Q.coeff m) = 0 :=
      (IsFractionRing.injective Rb K) (by simpa [α] using h2)
    exact Ideal.Quotient.eq_zero_iff_mem.1 h3
  have hdeg : (θ0 Q).totalDegree ≤ d :=
    (totalDegree_rename_le _ _).trans ((Finset.sup_mono (support_map_subset α Q)).trans hd)
  obtain ⟨L, _, _, cL, hL⟩ := Kollar.exists_mult_le_mult_localization_ker_eval ⟨𝔮, h𝔮⟩ (θ0 Q)
  refine hL.trans (Kollar.mult_localization_ker_eval_le_of_totalDegree_le cL ?_ ?_)
  · simpa using (map_injective _ (algebraMap K L).injective).ne hne
  · exact (Finset.sup_mono (support_map_subset (algebraMap K L) _)).trans hdeg

/-- An ideal of order `≤ m` is not contained in `𝔪^(m+1)`. -/
private theorem not_le_maximalIdeal_pow_succ_of_idealOrder_le {R : Type*} [CommRing R]
    [IsLocalRing R] {K : Ideal R} {m : ℕ} (h : idealOrder K ≤ m) :
    ¬ K ≤ maximalIdeal R ^ (m + 1) := by
  intro hK
  have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ idealOrder K :=
    le_iSup₂_of_le (f := fun (j : ℕ) (_ : K ≤ maximalIdeal R ^ j) => (j : ℕ∞)) (m + 1) hK le_rfl
  have h2 := h1.trans h
  norm_cast at h2
  omega

/-- The chart coordinates `x_i` vanish at every point of the centre in the chart's domain. -/
private theorem germ_x_mem_maximalIdeal {X : Scheme.{u}} {Z : X.IdealSheafData}
    (c : BlowupChartData Z) (hU : IsAffineOpen c.U) {p : X} (hpU : p ∈ c.U)
    (hpZ : p ∈ (Z.support : Set X)) (i : Fin c.r) :
    (X.presheaf.germ c.U p hpU).hom (c.x i) ∈ maximalIdeal (X.presheaf.stalk p) := by
  refine IsLocalRing.le_maximalIdeal
    (fun h => (IdealSheafData.stalk_eq_top_iff_notMem_support Z p).1 h hpZ) ?_
  rw [IdealSheafData.stalk_eq_map_germ Z p ⟨c.U, hU⟩ hpU, c.ideal_eq_span hU]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

/-- If `I_p ⊆ I_{Z,p}^m` and `ord_p I ≤ m` at a point `p` of the centre, then `I_p` contains,
up to a unit, a form `P(x_1, …, x_r)` of degree `m` whose dehomogenization at `x_ℓ` has a
coefficient not vanishing at `p`. -/
private theorem exists_isHomogeneous_germ_eval_mem {X : Scheme.{u}} {Z : X.IdealSheafData}
    (c : BlowupChartData Z) (hU : IsAffineOpen c.U) {p : X} (hpU : p ∈ c.U)
    (hpZ : p ∈ (Z.support : Set X)) (I : X.IdealSheafData) (m : ℕ)
    (hIZ : IdealSheafData.stalk I p ≤ IdealSheafData.stalk Z p ^ m) (hpm : multAt I p ≤ m)
    (ℓ : Fin c.r) :
    ∃ P : MvPolynomial (Fin c.r) Γ(X, c.U), P.IsHomogeneous m ∧
      (X.presheaf.germ c.U p hpU).hom (eval c.x P) ∈ IdealSheafData.stalk I p ∧
      dehomogenize Γ(X, c.U) ℓ P ∉
        Ideal.map C ((maximalIdeal (X.presheaf.stalk p)).comap
          (X.presheaf.germ c.U p hpU).hom) := by
  set ψ := (X.presheaf.germ c.U p hpU).hom
  have hZp : IdealSheafData.stalk Z p = Ideal.map ψ (Ideal.span (Set.range c.x)) := by
    rw [IdealSheafData.stalk_eq_map_germ Z p ⟨c.U, hU⟩ hpU, c.ideal_eq_span hU]
  obtain ⟨g, hgI, hgm⟩ := SetLike.not_le_iff_exists.mp
    (not_le_maximalIdeal_pow_succ_of_idealOrder_le (K := IdealSheafData.stalk I p) hpm)
  have hgZ : g ∈ Ideal.map ψ (Ideal.span (Set.range c.x) ^ m) := by
    rw [Ideal.map_pow, ← hZp]
    exact hIZ hgI
  let : Algebra Γ(X, c.U) (X.presheaf.stalk p) := ψ.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk p) (hU.primeIdealOf ⟨p, hpU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨p, hpU⟩
  obtain ⟨⟨b, s⟩, hbs⟩ := (IsLocalization.mem_map_algebraMap_iff
    (hU.primeIdealOf ⟨p, hpU⟩).asIdeal.primeCompl (X.presheaf.stalk p)).1 hgZ
  have hunit : IsUnit (ψ s) := IsLocalization.map_units (X.presheaf.stalk p) s
  change g * ψ s = ψ b at hbs
  obtain ⟨P, hPh, hPe⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous c.x (b : Γ(X, c.U))).1 b.2
  rw [← hPe] at hbs
  have hbm : ψ (eval c.x P) ∉ maximalIdeal (X.presheaf.stalk p) ^ (m + 1) := fun h =>
    hgm ((Ideal.mul_unit_mem_iff_mem _ hunit).1 (hbs ▸ h))
  exact ⟨P, hPh, hbs ▸ Ideal.mul_mem_right _ _ hgI, fun h =>
    hbm (map_eval_mem_pow_succ ψ _ c.x (germ_x_mem_maximalIdeal c hU hpU hpZ) hPh
      (mem_map_C_of_isHomogeneous_of_dehomogenize_mem _ hPh h))⟩

/-- **The chart computation.** Let `x_1, …, x_n` be local coordinates on an affine open `U`, the
first `r` of which generate `Z|_U`, and `q` a point of the chart `U_ℓ` over a point `p` of `Z`,
with `t` the germ of `π^*x_ℓ` at `q`, a nonzerodivisor. If `I_p ⊆ I_{Z,p}^m`, `ord_p I ≤ m`,
and `J · (t^m) = π^*I` at `q`, then `ord J ≤ m`. -/
private theorem idealOrder_le_of_chart {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {Z : X.IdealSheafData} (c : BlowupChartData Z)
    (hU : IsAffineOpen c.U) {n : ℕ} (x : Fin n → Γ(X, c.U))
    (hx : IsLocalCoordinates sX c.U x) (hrn : c.r ≤ n) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i))
    (ℓ : Fin c.r) {q : blowUp Z} (hq : q ∈ c.chart ℓ)
    (hpZ : blowUpToBase Z q ∈ (Z.support : Set X)) (I : X.IdealSheafData) (m : ℕ)
    (hIZ : IdealSheafData.stalk I (blowUpToBase Z q) ≤
      IdealSheafData.stalk Z (blowUpToBase Z q) ^ m)
    (hpm : multAt I (blowUpToBase Z q) ≤ m) (J : Ideal ((blowUp Z).presheaf.stalk q))
    (hJ : J * Ideal.span {(blowUp Z).presheaf.germ (c.chart ℓ) q hq (c.chartPullback ℓ (c.x ℓ)) ^ m}
      = Ideal.map ((blowUpToBase Z).stalkMap q).hom (IdealSheafData.stalk I (blowUpToBase Z q)))
    (ht : IsRegular ((blowUp Z).presheaf.germ (c.chart ℓ) q hq (c.chartPullback ℓ (c.x ℓ)))) :
    idealOrder J ≤ m := by
  classical
  set p := blowUpToBase Z q
  have hpU : p ∈ c.U := c.chart_le ℓ hq
  set ψ := (X.presheaf.germ c.U p hpU).hom
  set t := (blowUp Z).presheaf.germ (c.chart ℓ) q hq (c.chartPullback ℓ (c.x ℓ))
  set φ := ((blowUpToBase Z).stalkMap q).hom with hφ
  have : IsLocalHom φ := by
    rw [hφ]
    infer_instance
  have hxm := germ_x_mem_maximalIdeal c hU hpU hpZ
  obtain ⟨P, hPh, hb, hQ⟩ := exists_isHomogeneous_germ_eval_mem c hU hpU hpZ I m hIZ hpm ℓ
  set Q := dehomogenize Γ(X, c.U) ℓ P
  have hW : IsAffineOpen (c.chart ℓ) := isAffineOpen_chart c hU ℓ
  let : Algebra Γ(blowUp Z, c.chart ℓ) ((blowUp Z).presheaf.stalk q) :=
    ((blowUp Z).presheaf.germ (c.chart ℓ) q hq).hom.toAlgebra
  have : IsLocalization.AtPrime ((blowUp Z).presheaf.stalk q)
    (hW.primeIdealOf ⟨q, hq⟩).asIdeal := hW.isLocalization_stalk ⟨q, hq⟩
  obtain ⟨hsurj, hker⟩ := chartPresentation_surjective_and_ker c sX hU x hx hrn hcx ℓ
  have hker' : RingHom.ker (chartPresentation c ℓ) ≤
      Ideal.map C ((maximalIdeal (X.presheaf.stalk p)).comap ψ) := by
    rw [hker, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact sub_mem (Ideal.mem_map_of_mem _ (hxm i.1))
      (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hxm ℓ)))
  have hC : ∀ a, chartPresentation c ℓ (C a) ∈ (hW.primeIdealOf ⟨q, hq⟩).asIdeal ↔
      a ∈ (maximalIdeal (X.presheaf.stalk p)).comap ψ := by
    intro a
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((blowUp Z).presheaf.stalk q)
      (hW.primeIdealOf ⟨q, hq⟩).asIdeal, Ideal.mem_comap]
    have h1 : algebraMap Γ(blowUp Z, c.chart ℓ) ((blowUp Z).presheaf.stalk q)
        (chartPresentation c ℓ (C a)) = φ (ψ a) := by
      rw [c.stalkMap_germ ℓ hq a]
      simp [chartPresentation, BlowupChartData.chartPullback]
      rfl
    rw [h1, ← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap]
  have hmult := mult_algebraMap_pres_le (S := (blowUp Z).presheaf.stalk q)
    (chartPresentation c ℓ) hsurj _ hker' _ hC Q hQ (totalDegree_dehomogenize_le ℓ hPh)
  set h := algebraMap Γ(blowUp Z, c.chart ℓ) ((blowUp Z).presheaf.stalk q)
    (chartPresentation c ℓ Q)
  have e1 : φ (ψ (eval c.x P)) = h * t ^ m := by
    rw [c.stalkMap_germ ℓ hq, c.chartPullback_eval_eq ℓ hPh, map_mul, map_pow, mul_comm]
    rfl
  have hmem : φ (ψ (eval c.x P)) ∈ J * Ideal.span {t ^ m} := hJ ▸ Ideal.mem_map_of_mem _ hb
  obtain ⟨j, hj, hjt⟩ := Ideal.mem_mul_span_singleton.1 hmem
  have hjh : j = h := (ht.pow m).2 (show j * t ^ m = h * t ^ m by rw [hjt, e1])
  exact (Kollar.idealOrder_antitone ((Ideal.span_singleton_le_iff_mem _).2 (hjh ▸ hj))).trans hmult

end Chart

/-- A generator of a principal ideal generated by a regular element is regular. -/
private theorem isRegular_of_span_singleton_eq {R : Type*} [CommRing R] {t g : R}
    (h : Ideal.span {t} = Ideal.span {g}) (hg : IsRegular g) : IsRegular t := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self t)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self g)
  have hab : b * a = 1 := by
    refine hg.2 ?_
    change b * a * g = 1 * g
    rw [one_mul, mul_assoc, ha, hb]
  rw [← ha]
  exact (isUnit_iff_exists_inv.2 ⟨b, (mul_comm a b).trans hab⟩).isRegular.mul hg

/-- The divisor `∑_j m_j F_j` of the controlled transform is `m F` when `ord_Z I = m`. -/
private theorem controlledTransformDivisorIdeal_eq_pow {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (m : ℕ) (hIZ : OrderAlongEq I (Z.support : Set X) m) :
    controlledTransformDivisorIdeal Z I = Z.comap (blowUpToBase Z) ^ m := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  let := Fintype.ofFinite (componentsOf (Z.support : Set X))
  have key : ∀ y, IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
      IdealSheafData.stalk (Z.comap (blowUpToBase Z) ^ m) y := by
    intro y
    set x := blowUpToBase Z y
    have hD : IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
        ∏ W : componentsOf (Z.support : Set X), Ideal.map ((blowUpToBase Z).stalkMap y).hom
          (IdealSheafData.stalk (componentsFamily (Z.support : Set X) W) x) ^
            (orderAlong I W.2.1.1).toNat := by
      unfold controlledTransformDivisorIdeal
      rw [finprod_eq_prod_of_fintype, stalk_prod]
      exact Finset.prod_congr rfl fun W _ => by
        rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
    rw [hD, IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
    by_cases hx : x ∈ (Z.support : Set X)
    · obtain ⟨W0, hW0, hxW0, huniq, hstalk, -⟩ := exists_component_through sX hX Z hZ I x hx
      rw [Finset.prod_eq_single (⟨W0, hW0⟩ : componentsOf (Z.support : Set X))]
      · rw [hstalk, hIZ W0 hW0]
        rfl
      · intro W _ hne
        have : x ∉ (W : Set X) := fun hxW => hne (Subtype.ext (huniq W W.2 hxW))
        rw [stalk_componentsFamily_eq_top Z W.2 this, Ideal.map_top, ← Ideal.one_eq_top, one_pow]
      · exact absurd (Finset.mem_univ _)
    · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support Z x).2 hx, Ideal.map_top,
        ← Ideal.one_eq_top, one_pow]
      refine Finset.prod_eq_one fun W _ => ?_
      have : x ∉ (W : Set X) := fun hxW => hx (W.2.1.2 hxW)
      rw [stalk_componentsFamily_eq_top Z W.2 this, Ideal.map_top, ← Ideal.one_eq_top, one_pow]
  exact le_antisymm (IdealSheafData.le_of_stalk_le _ _ fun y => (key y).le)
    (IdealSheafData.le_of_stalk_le _ _ fun y => (key y).ge)

/-- The pointwise bound `ord_q π⁻¹_{Z*}I ≤ m` at a point `q` over the centre, given
`I_p ⊆ I_{Z,p}^m`, `ord_p I ≤ m` and `π⁻¹_{Z*}I · (𝒪(-F))^m = π^*I` at `q`. -/
private theorem multAt_controlledTransform_le_of_mem_support {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (Z : X.IdealSheafData)
    [Smooth (Z.subschemeι ≫ sX)] (I : X.IdealSheafData) (m : ℕ) {q : blowUp Z}
    (hp : blowUpToBase Z q ∈ (Z.support : Set X))
    (hIZ : IdealSheafData.stalk I (blowUpToBase Z q) ≤
      IdealSheafData.stalk Z (blowUpToBase Z q) ^ m)
    (hpm : multAt I (blowUpToBase Z q) ≤ m)
    (hst : IdealSheafData.stalk (controlledTransform Z I) q *
      IdealSheafData.stalk (Z.comap (blowUpToBase Z)) q ^ m =
      Ideal.map ((blowUpToBase Z).stalkMap q).hom (IdealSheafData.stalk I (blowUpToBase Z q))) :
    multAt (controlledTransform Z I) q ≤ m := by
  set π := blowUpToBase Z
  set p := π q with hp_def
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap π) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
  obtain ⟨g0, hg0, hg0s⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hE q
  obtain ⟨z, hz⟩ : p ∈ Set.range Z.subschemeι := by
    rw [Z.range_subschemeι]
    exact hp
  obtain ⟨nX, hnX⟩ := Stacks.RelativeAssassin.exists_nat_eq_topologicalKrullDimAt X k sX
    (Z.subschemeι z)
  obtain ⟨nZ, hnZ⟩ := Stacks.RelativeAssassin.exists_nat_eq_topologicalKrullDimAt Z.subscheme k
    (Z.subschemeι ≫ sX) z
  have hle' :=
    Stacks.AlgebraicGeometry.LimitFibreDimensionBound.topologicalKrullDimAt_le_of_isInducing
      Z.subschemeι.isClosedEmbedding.isInducing z
  rw [hnX, hnZ] at hle'
  have hle'' : nZ ≤ nX := by exact_mod_cast hle'
  have hc : topologicalKrullDimAt X (Z.subschemeι z) =
      topologicalKrullDimAt Z.subscheme z + ((nX - nZ : ℕ) : WithBot ℕ∞) := by
    rw [hnX, hnZ, ← Nat.cast_add, Nat.add_sub_cancel' hle'']
  obtain ⟨U, hU, hzU, x, hx, hcut⟩ := Bridges.exists_isLocalCoordinates_adapted sX Z z hc
  suffices key : ∀ {n : ℕ} (x : Fin n → Γ(X, U)), IsLocalCoordinates sX U x →
      Bridges.IsCutOutByFirst Z U x (nX - nZ) →
      multAt (controlledTransform Z I) q ≤ m from key x hx hcut
  intro n x hx hcut
  have hrn : min (nX - nZ) n ≤ n := min_le_right _ _
  let cd : BlowupChartData Z :=
    { U := U
      r := min (nX - nZ) n
      x := fun i => x (Fin.castLE hrn i)
      generates := fun V hV => by
        rw [hcut V hV]
        congr 1
        ext s
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨⟨i, lt_min hi i.2⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          exact ⟨Fin.castLE hrn j, lt_of_lt_of_le j.2 (min_le_left _ _), rfl⟩ }
  have hqU : q ∈ π ⁻¹ᵁ cd.U := by
    change π q ∈ U
    rw [← hp_def, ← hz]
    exact hzU
  rw [← MMP.Flips.ResolutionInputs.iSup_chart_eq_preimage cd] at hqU
  obtain ⟨ℓ, hqℓ⟩ := TopologicalSpace.Opens.mem_iSup.mp hqU
  set t := (blowUp Z).presheaf.germ (cd.chart ℓ) q hqℓ (cd.chartPullback ℓ (cd.x ℓ))
  have hEq : IdealSheafData.stalk (Z.comap π) q = Ideal.span {t} :=
    cd.stalk_comap_eq_span hU ℓ hqℓ
  have htreg : IsRegular t := isRegular_of_span_singleton_eq (by rw [← hEq, hg0s]) hg0
  have hJ : IdealSheafData.stalk (controlledTransform Z I) q * Ideal.span {t ^ m} =
      Ideal.map (π.stalkMap q).hom (IdealSheafData.stalk I p) := by
    rw [← Ideal.span_singleton_pow, ← hEq, hst]
  exact idealOrder_le_of_chart sX cd hU x hx hrn (fun _ => rfl) ℓ hqℓ hp I m hIZ hpm _ hJ htreg

/-- The pointwise bound `ord_q π⁻¹_{Z*}I ≤ maxord I` at every point `q` of the blow-up. -/
private theorem multAt_controlledTransform_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)]
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (I : X.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) (hZI : OrderAlongEq I (Z.support : Set X) (maxOrder I))
    (q : blowUp Z) : multAt (controlledTransform Z I) q ≤ maxOrder I := by
  have hX : MMP.Mori.IsSmoothScheme sX := isSmoothScheme_of_smooth sX
  have hZs : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX) := isSmoothScheme_of_smooth _
  by_cases hM : maxOrder I = ⊤
  · simp [hM]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hM
  rw [← hm]
  have hpm : multAt I (blowUpToBase Z q) ≤ m := by
    rw [hm]
    exact le_iSup₂ (f := fun x (_ : x ∈ Set.univ) => multAt I x) _ (Set.mem_univ _)
  have hst : IdealSheafData.stalk (controlledTransform Z I) q *
      IdealSheafData.stalk (Z.comap (blowUpToBase Z)) q ^ m =
      Ideal.map ((blowUpToBase Z).stalkMap q).hom (IdealSheafData.stalk I (blowUpToBase Z q)) := by
    rw [← IdealSheafData.stalk_pow, ← controlledTransformDivisorIdeal_eq_pow sX hX Z hZs I m
      fun W hW => (hZI W hW).trans hm.symm, ← IdealSheafData.stalk_mul,
      controlledTransform_mul_eq sX hX Z hZs hcodim I hI, IdealSheafData.stalk_comap]
  by_cases hp : blowUpToBase Z q ∈ (Z.support : Set X)
  · obtain ⟨W0, hW0, -, -, -, hle⟩ := exists_component_through sX hX Z hZs I _ hp
    exact multAt_controlledTransform_le_of_mem_support sX Z I m hp
      (hle m ((hZI W0 hW0).trans hm.symm).ge) hpm hst
  rw [IdealSheafData.stalk_comap, (IdealSheafData.stalk_eq_top_iff_notMem_support Z _).2 hp,
    Ideal.map_top, ← Ideal.one_eq_top, one_pow, mul_one] at hst
  have hiso : IsIso ((blowUpToBase Z).stalkMap q) :=
    isIso_stalkMap_of_isIso_morphismRestrict _ (isIso_blowUpToBase_restrict_compl_support Z)
      (show q ∈ blowUpToBase Z ⁻¹ᵁ Z.support.compl from hp)
  unfold multAt
  rw [hst]
  exact (idealOrder_map_le _
    (asIso ((blowUpToBase Z).stalkMap q)).commRingCatIsoToRingEquiv.bijective _).trans hpm

/-- On a quasi-compact smooth scheme over a field, if a smooth center `Z` with components of
codimension `≥ 1` satisfies `ord_Z I = maxord I` for an ideal sheaf `I` nonzero on every
irreducible component, then the maximal order of the controlled transform of `I` along the
blow-up of `Z` is at most `maxord I`. -/
@[mmp "lem_kr3c_max_order_transform_le"]
public theorem maxOrder_controlledTransform_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)]
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (I : X.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) (hZI : OrderAlongEq I (Z.support : Set X) (maxOrder I)) :
    maxOrder (controlledTransform Z I) ≤ maxOrder I :=
  iSup₂_le fun q _ => multAt_controlledTransform_le sX Z hcodim I hI hZI q

/-- When `ord_Z I = m`, the birational transform of `(I, m)` is the controlled transform of `I`,
marked by `m`. -/
private theorem birationalTransform_eq_controlledTransform {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (m : ℕ) (hIZ : OrderAlongEq I (Z.support : Set X) m) :
    MarkedIdeal.birationalTransform Z ⟨I, m⟩ = ⟨controlledTransform Z I, m⟩ := by
  change (⟨idealColon _ _, m⟩ : MarkedIdeal _) = ⟨idealColon _ _, m⟩
  rw [controlledTransformDivisorIdeal_eq_pow sX hX Z hZ I m hIZ]

/-- The order along an irreducible set is at most the maximal order. -/
private theorem orderAlong_le_maxOrder {X : Scheme.{u}} (I : X.IdealSheafData) {W : Set X}
    (hW : IsIrreducible W) : orderAlong I hW ≤ maxOrder I :=
  le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) hW.genericPoint (Set.mem_univ _)

/-- A smooth blow-up sequence of order `m` starting with `(X, I, E)` is one of order `≥ m`
starting with `(X, I, m, E)`, and its iterated controlled transform is the ideal of the
iterated marked transform. -/
private theorem isOrderGeMarkedTripleSeq_of_isOrderMTripleSeq {k : Type u} [Field k] (m : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X), B.IsOrderMTripleSeq sX I E m →
      B.IsOrderGeMarkedTripleSeq sX ⟨I, m⟩ E ∧
        (B.markedTransform ⟨I, m⟩).I = B.controlledTransform I := by
  intro X B
  induction B with
  | nil X => exact fun sX I E h => ⟨h, rfl⟩
  | cons Z B ih =>
    intro sX I E h
    obtain ⟨hT, hZ, hc, hs, hEq, hB⟩ := h
    obtain ⟨-, hX, hlft, hqc, -⟩ := id hT
    have key := birationalTransform_eq_controlledTransform sX hX Z hZ I m hEq
    obtain ⟨h1, h2⟩ := ih _ _ _ hB
    refine ⟨⟨hT, hZ, hc, hs, fun W hW => (hEq W hW).ge, ?_⟩, ?_⟩
    · rwa [key]
    · change (B.markedTransform (MarkedIdeal.birationalTransform Z ⟨I, m⟩)).I = _
      rwa [key]

/-- A smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`, where
`maxord I ≤ m`, is one of order `m` starting with `(X, I, E)`. -/
private theorem isOrderMTripleSeq_of_isOrderGeMarkedTripleSeq {k : Type u} [Field k] (m : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X), maxOrder I ≤ m →
      B.IsOrderGeMarkedTripleSeq sX ⟨I, m⟩ E → B.IsOrderMTripleSeq sX I E m := by
  intro X B
  induction B with
  | nil X => exact fun sX I E _ h => h
  | cons Z B ih =>
    intro sX I E hmax h
    obtain ⟨hT, hZ, hc, hs, hGe, hB⟩ := h
    obtain ⟨-, hX, hlft, hqc, -, hI, -⟩ := id hT
    have hEq : OrderAlongEq I (Z.support : Set _) m := fun W hW =>
      le_antisymm ((orderAlong_le_maxOrder I _).trans hmax) (hGe W hW)
    have hB' : B.IsOrderGeMarkedTripleSeq (blowUpToBase Z ≫ sX) ⟨controlledTransform Z I, m⟩
        (E.totalTransform Z) :=
      birationalTransform_eq_controlledTransform sX hX Z hZ I m hEq ▸ hB
    have hmax' : maxOrder (controlledTransform Z I) ≤ m := by
      have := Aux.smooth_of_isSmoothScheme' sX hX
      have := Aux.smooth_of_isSmoothScheme' _ hZ
      refine (maxOrder_controlledTransform_le sX Z hc I hI fun W hW => ?_).trans hmax
      exact le_antisymm (orderAlong_le_maxOrder I _) (hmax.trans (hEq W hW).ge)
    exact ⟨hT, hZ, hc, hs, hEq, ih _ _ _ hmax' hB'⟩

namespace ClosedBlowupSequence

/-- For a triple `(X, I, E)` with `m = maxord I`, a blow-up sequence is a smooth blow-up sequence
of order `≥ m` starting with `(X, I, m, E)` if and only if it is a smooth blow-up sequence of
order `m` starting with `(X, I, E)`, and then the iterated marked transform of `(I, m)` has the
iterated controlled transform of `I` as its ideal (Kollár, Remark 3.67). -/
@[mmp "lem_kr3c_marked_unmarked_sequences_coincide"]
public theorem isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
    (hI : IsTriple sX I E) (m : ℕ) (hm : maxOrder I = m) (B : ClosedBlowupSequence X) :
    (B.IsOrderGeMarkedTripleSeq sX ⟨I, m⟩ E ↔ B.IsOrderMTripleSeq sX I E m) ∧
      (B.IsOrderMTripleSeq sX I E m →
        (B.markedTransform ⟨I, m⟩).I = B.controlledTransform I) :=
  ⟨⟨isOrderMTripleSeq_of_isOrderGeMarkedTripleSeq m B sX I E hm.le,
    fun h => (isOrderGeMarkedTripleSeq_of_isOrderMTripleSeq m B sX I E h).1⟩,
    fun h => (isOrderGeMarkedTripleSeq_of_isOrderMTripleSeq m B sX I E h).2⟩

end ClosedBlowupSequence

end MMP.Resolution

end
