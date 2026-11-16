/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic

/-!
# Isomorphic divisorial sheaves and linear equivalence

On an integral locally Noetherian normal quasi-compact scheme `X`, a morphism of divisorial
sheaves `𝒪_X(D₁) ⟶ 𝒪_X(D₂)` is multiplication by a rational function, and an isomorphism
`𝒪_X(D₁) ≅ 𝒪_X(D₂)` forces `D₁ ∼ D₂` (the converse of
`MMP.Mori.Divisor.LinearlyEquivalent.divisorialSheafIso`). Consequently any two canonical
divisors of a smooth integral scheme are linearly equivalent. This is used for the independence
of the log discrepancy condition of FA 3.0.2 from the choice of the canonical divisor
(`MMP.Flips.isGermLogDiscrepancyVector_iff_of_isCanonicalDivisor`).

## Main results

* `MMP.Flips.exists_eq_mul_of_divisorialSheaf_hom`: a morphism `𝒪_X(D₁) ⟶ 𝒪_X(D₂)` is
  multiplication by some `u ∈ K(X)`.
* `MMP.Flips.exists_divisorialSection_ord_eq`: local sections of `𝒪_X(D)` of exact order
  `-d_E` along a prime divisor `E`.
* `MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso`: `𝒪_X(D₁) ≅ 𝒪_X(D₂)` implies
  `D₁ ∼ D₂`.
* `MMP.Flips.nonempty_iso_of_restrict_iso`: restriction to the open subscheme `X` reflects
  isomorphisms of `𝒪_X`-modules.
* `MMP.Flips.linearlyEquivalent_of_isCanonicalDivisor`: two canonical divisors of a smooth
  integral scheme are linearly equivalent.

## Implementation notes

`u` is the value at the generic point of the image of the section `1` of `𝒪_X(D₁)` over the open
complement of `Supp D₁` (`MMP.Flips.divisorSuppCompl`); near the generic point every section of
`𝒪_X(D₁)` is a regular function times `1` by algebraic Hartogs
(`MMP.Mori.Divisor.IsDivisorialSection.exists_eq`). Integrality makes every nonempty open contain
the generic point, so sections are compared there.

## References

* [R. Hartshorne, *Algebraic geometry*][Har77], II.6.13
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Order MMP.Mori

universe u

namespace MMP.Flips

variable {X : Scheme.{u}}

/-- The generic point of a prime divisor `E` lies on no other prime divisor. -/
theorem eq_of_genericPoint_mem_primeDivisor_support {E E' : Mori.PrimeDivisor X}
    (h : E.genericPoint ∈ E'.support) : E = E' := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have hle : E.genericPoint ≤ E'.genericPoint := specializes_iff_mem_closure.mpr h
  by_contra hne
  have hlt : E.genericPoint < E'.genericPoint := lt_iff_le_not_ge.mpr ⟨hle, fun h' =>
    hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (Specializes.antisymm h' hle).eq)⟩
  have hstep := coheight_add_one_le hlt
  rw [E.coheight_genericPoint, E'.coheight_genericPoint] at hstep
  exact absurd hstep (by decide)

/-- A prime divisor contains its generic point. -/
theorem primeDivisor_genericPoint_mem_support (E : Mori.PrimeDivisor X) :
    E.genericPoint ∈ E.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

variable [IsLocallyNoetherian X] [IsNormal X]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- On an irreducible scheme, every point lies in the irreducible component. -/
private theorem mem_irreducibleComponent [IrreducibleSpace X] (Z : irreducibleComponents X)
    (x : X) : x ∈ Z.1 := by
  have h := Z.2
  simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
  rw [h]
  trivial

/-- On an irreducible scheme, a unit of `K(X)` with prescribed order `n` along a prime divisor
`E`: a power of a uniformizer of `𝒪_{X,E}`. -/
theorem exists_primeDivisor_ord_eq [IrreducibleSpace X] (E : Mori.PrimeDivisor X) (n : ℤ) :
    ∃ t : (RationalFunctions X)ˣ, E.ord t = n := by
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  have hmem : ∀ Z : irreducibleComponents X, E.genericPoint ∈ Z.1 := fun Z =>
    mem_irreducibleComponent Z _
  let w : RationalFunctions X := fun Z => (stalkToRationalFunctions X (hmem Z)).hom ϖ
  have hw : IsUnit w := Pi.isUnit_iff.mpr fun Z => isUnit_of_ne_zero_stalk Z fun h0 =>
    hϖ.ne_zero (stalkToRationalFunctions_injective (hmem Z) (h0.trans (map_zero _).symm))
  refine ⟨hw.unit ^ n, ?_⟩
  rw [PrimeDivisor.ord_zpow, E.ord_eq_one_of_irreducible hϖ rfl, smul_eq_mul, mul_one]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- On an irreducible scheme, the generic point lies on no prime divisor. -/
theorem componentGenericPoint_notMem_support [IrreducibleSpace X] (Z : irreducibleComponents X)
    (E : Mori.PrimeDivisor X) : componentGenericPoint X Z ∉ E.support := by
  intro h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have hall : ∀ y : X, y ≤ E.genericPoint := fun y => by
    refine specializes_iff_mem_closure.mpr ?_
    refine closure_minimal (Set.singleton_subset_iff.mpr h) isClosed_closure ?_
    rw [(isGenericPoint_componentGenericPoint X Z).def]
    exact mem_irreducibleComponent Z y
  have h0 := Order.coheight_eq_zero.mpr fun y _ => hall y
  rw [E.coheight_genericPoint] at h0
  exact one_ne_zero h0

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The open complement of the support of a divisor. -/
def divisorSuppCompl (D : Divisor X) : X.Opens := ⟨(D.supp : Set X)ᶜ, D.isClosed_supp.isOpen_compl⟩

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A divisor has coefficient `0` along every prime divisor meeting an open inside the
complement of its support. -/
theorem coeff_eq_zero_of_le_divisorSuppCompl {D : Divisor X} {W : X.Opens}
    (hW : W ≤ divisorSuppCompl D)
    {E : Mori.PrimeDivisor X} (hE : (E.support ∩ W).Nonempty) : D.coeff E = 0 := by
  obtain ⟨x, hxE, hxW⟩ := hE
  by_contra h
  exact hW hxW (DivisorWithCoeffs.support_subset_supp h hxE)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- On an irreducible scheme, the generic point lies off the support of every divisor. -/
theorem componentGenericPoint_mem_divisorSuppCompl [IrreducibleSpace X] (D : Divisor X)
    (Z : irreducibleComponents X) : componentGenericPoint X Z ∈ divisorSuppCompl D := fun h => by
  obtain ⟨E, -, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  exact componentGenericPoint_notMem_support Z E hmem

/-- The section `1` of `𝒪_X(D)` over the complement of `Supp D`. -/
def divisorialSheafOne (D : Divisor X) : Γ(D.divisorialSheaf, divisorSuppCompl D) :=
  ⟨1, fun E hE => Or.inr (by
    change WithZero.exp _ ≤ E.valuation 1
    rw [map_one, coeff_eq_zero_of_le_divisorSuppCompl le_rfl hE, neg_zero, WithZero.exp_zero])⟩

/-- **A morphism of divisorial sheaves is multiplication by a rational function.** On an integral
locally Noetherian normal scheme, for every morphism `α : 𝒪_X(D₁) ⟶ 𝒪_X(D₂)` there is `u ∈ K(X)`
with `α(s) = u · s` for every section `s` of `𝒪_X(D₁)`: on the open `U₁` where `D₁` vanishes,
`u = α(1)`, and every section is, near the generic point, a regular function times `1` by
algebraic Hartogs. -/
theorem exists_eq_mul_of_divisorialSheaf_hom [IsIntegral X] {D₁ D₂ : Divisor X}
    (α : D₁.divisorialSheaf ⟶ D₂.divisorialSheaf) :
    ∃ u : RationalFunctions X, ∀ (V : X.Opens) (s : Γ(D₁.divisorialSheaf, V))
      (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V}),
      Divisor.secVal D₂ V (α.app V s) Z = u Z.1 * Divisor.secVal D₁ V s Z := by
  set U₁ := divisorSuppCompl D₁
  have hU₁ : ∀ Z, componentGenericPoint X Z ∈ U₁ := componentGenericPoint_mem_divisorSuppCompl D₁
  set one₁ := divisorialSheafOne D₁
  have nat : ∀ {V W : X.Opens} (i : W ⟶ V) (s : Γ(D₁.divisorialSheaf, V)),
      α.app W (D₁.divisorialSheaf.presheaf.map i.op s) =
        D₂.divisorialSheaf.presheaf.map i.op (α.app V s) := fun i s => by
    simpa using ConcreteCategory.congr_hom (α.mapPresheaf.naturality i.op) s
  refine ⟨fun Z => Divisor.secVal D₂ U₁ (α.app U₁ one₁) ⟨Z, hU₁ Z⟩, ?_⟩
  intro V s Z
  set W := V ⊓ U₁
  have hZW : componentGenericPoint X Z.1 ∈ W := ⟨Z.2, hU₁ Z.1⟩
  let iV : W ⟶ V := homOfLE inf_le_left
  let iU : W ⟶ U₁ := homOfLE inf_le_right
  set s' := D₁.divisorialSheaf.presheaf.map iV.op s with hs'def
  have hs0 : (0 : Divisor X).IsDivisorialSection W (Divisor.secVal D₁ W s') := fun E hE => by
    have := (s' : D₁.divisorialSubmodule W).2 E hE
    rwa [coeff_eq_zero_of_le_divisorSuppCompl inf_le_right hE] at this
  obtain ⟨r, hr⟩ := hs0.exists_eq
  have hs' : s' = r • D₁.divisorialSheaf.presheaf.map iU.op one₁ := by
    apply Subtype.ext
    funext Z'
    change _ = X.presheaf.germ W _ Z'.2 r * 1
    exact (congrFun hr Z').symm.trans (mul_one _).symm
  have key : D₂.divisorialSheaf.presheaf.map iV.op (α.app V s) =
      r • D₂.divisorialSheaf.presheaf.map iU.op (α.app U₁ one₁) := by
    rw [← nat, ← hs'def, hs', Scheme.Modules.Hom.app_smul, nat]
  change Divisor.secVal D₂ W (D₂.divisorialSheaf.presheaf.map iV.op (α.app V s)) ⟨Z.1, hZW⟩ =
    Divisor.secVal D₂ U₁ (α.app U₁ one₁) ⟨Z.1, hU₁ Z.1⟩ * Divisor.secVal D₁ W s' ⟨Z.1, hZW⟩
  rw [congrArg (fun t => Divisor.secVal D₂ W t ⟨Z.1, hZW⟩) key, ← congrFun hr ⟨Z.1, hZW⟩]
  change X.presheaf.germ W _ hZW r * _ = _ * X.presheaf.germ W _ hZW r
  exact mul_comm _ _

/-- On an irreducible locally Noetherian normal (and quasi-compact) scheme, every divisor `D` has,
along every prime divisor `E`, a local section of `𝒪_X(D)` of order exactly `-d_E`: a unit
`t ∈ K(X)` with `v_E(t) = -d_E`, on the open complement of the finitely many other prime divisors
along which `D` or `div t` is nonzero. -/
theorem exists_divisorialSection_ord_eq [IrreducibleSpace X] [CompactSpace X] (D : Divisor X)
    (E : Mori.PrimeDivisor X) :
    ∃ (U : X.Opens) (_ : (E.support ∩ U).Nonempty) (t : (RationalFunctions X)ˣ),
      E.ord t = -D.coeff E ∧
      D.IsDivisorialSection U (fun Z => (t : RationalFunctions X) Z.1) := by
  classical
  obtain ⟨t, ht⟩ := exists_primeDivisor_ord_eq E (-D.coeff E)
  set S : Set (Mori.PrimeDivisor X) := {E' | E' ≠ E ∧ (D.coeff E' ≠ 0 ∨ E'.ord t ≠ 0)}
  have hS : S.Finite := by
    refine ((D.support.finite_toSet).union (finite_ord_ne_zero t)).subset ?_
    rintro E' ⟨-, h | h⟩
    · exact Or.inl (Finsupp.mem_support_iff.mpr h)
    · exact Or.inr h
  have hcl : IsClosed (⋃ E' ∈ S, E'.support) :=
    hS.isClosed_biUnion fun E' _ => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isClosed_closure
  let U : X.Opens := ⟨(⋃ E' ∈ S, E'.support)ᶜ, hcl.isOpen_compl⟩
  have hηU : E.genericPoint ∈ U := by
    change E.genericPoint ∉ ⋃ E' ∈ S, E'.support
    simp only [Set.mem_iUnion, not_exists]
    intro E' hE' hmem
    exact hE'.1 (eq_of_genericPoint_mem_primeDivisor_support hmem).symm
  refine ⟨U, ⟨_, primeDivisor_genericPoint_mem_support E, hηU⟩, t, ht, ?_⟩
  refine fun E' hE' => Or.inr ?_
  rw [E'.valuation_component t, WithZero.exp_le_exp]
  by_cases h : E' = E
  · subst h
    rw [ht]
  · have hnot : E' ∉ S := by
      rintro hmem
      obtain ⟨x, hxE', hxU⟩ := hE'
      exact hxU (Set.mem_biUnion hmem hxE')
    simp only [S, Set.mem_ofPred_eq, not_and, not_or, not_not] at hnot
    obtain ⟨h1, h2⟩ := hnot h
    rw [h1, h2, neg_zero]

/-- If a morphism `𝒪_X(A) ⟶ 𝒪_X(B)` is multiplication by a unit `w ∈ K(X)`, then
`-b_E ≤ v_E(w) - a_E` along every prime divisor `E`. -/
theorem neg_coeff_le_ord_sub_of_eq_mul [IsIntegral X] [CompactSpace X] {A B : Divisor X}
    (β : A.divisorialSheaf ⟶ B.divisorialSheaf) (w : (RationalFunctions X)ˣ)
    (hβ : ∀ (V : X.Opens) (s : Γ(A.divisorialSheaf, V))
      (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V}),
      Divisor.secVal B V (β.app V s) Z = (w : RationalFunctions X) Z.1 * Divisor.secVal A V s Z)
    (E : Mori.PrimeDivisor X) : -B.coeff E ≤ E.ord w - A.coeff E := by
  obtain ⟨U, hE, t, ht, hts⟩ := exists_divisorialSection_ord_eq A E
  let σ : Γ(A.divisorialSheaf, U) := ⟨fun Z => (t : RationalFunctions X) Z.1, hts⟩
  have hmem := E.componentGenericPoint_mem_of_nonempty hE
  have key : E.OrdGE (-B.coeff E) (Divisor.secVal B U (β.app U σ) ⟨E.component, hmem⟩) :=
    (β.app U σ : B.divisorialSubmodule U).2 E hE
  rw [hβ U σ ⟨E.component, hmem⟩] at key
  rcases key with h0 | h
  · exact absurd h0 (((Pi.isUnit_iff.mp w.isUnit) E.component).mul
      ((Pi.isUnit_iff.mp t.isUnit) E.component)).ne_zero
  · rw [map_mul, E.valuation_component, E.valuation_component, ← WithZero.exp_add,
      WithZero.exp_le_exp, ht] at h
    linarith

/-- **Isomorphic divisorial sheaves come from linearly equivalent divisors.** On an integral
Noetherian normal scheme, `𝒪_X(D₁) ≅ 𝒪_X(D₂)` implies `D₁ ∼ D₂`: the isomorphism and its inverse
are multiplication by mutually inverse rational functions `u`, `u⁻¹`
(`MMP.Flips.exists_eq_mul_of_divisorialSheaf_hom`), and testing on local sections of exact order
along each prime divisor `E` (`MMP.Flips.exists_divisorialSection_ord_eq`) gives
`d₁_E = d₂_E + v_E(u)`. -/
theorem linearlyEquivalent_of_divisorialSheaf_iso [IsIntegral X] [CompactSpace X]
    {D₁ D₂ : Divisor X} (α : D₁.divisorialSheaf ≅ D₂.divisorialSheaf) :
    D₁.LinearlyEquivalent D₂ := by
  obtain ⟨u, hu⟩ := exists_eq_mul_of_divisorialSheaf_hom α.hom
  obtain ⟨u', hu'⟩ := exists_eq_mul_of_divisorialSheaf_hom α.inv
  have hinv : u' * u = 1 := by
    funext Z
    have hZ := componentGenericPoint_mem_divisorSuppCompl D₁ Z
    have h1 := hu' _ (α.hom.app _ (divisorialSheafOne D₁)) ⟨Z, hZ⟩
    have h3 : α.inv.app _ (α.hom.app _ (divisorialSheafOne D₁)) = divisorialSheafOne D₁ := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, α.hom_inv_id]
      rfl
    rw [h3, hu _ _ ⟨Z, hZ⟩, ← mul_assoc] at h1
    change (1 : X.presheaf.stalk _) = u' Z * u Z * 1 at h1
    exact (h1.trans (mul_one _)).symm
  have hunit : IsUnit u := ⟨⟨u, u', (mul_comm u u').trans hinv, hinv⟩, rfl⟩
  set v := hunit.unit
  have h₁ := neg_coeff_le_ord_sub_of_eq_mul α.hom v hu
  have h₂ := neg_coeff_le_ord_sub_of_eq_mul α.inv v⁻¹ (by
    intro V s Z
    rw [hu' V s Z, Units.inv_eq_of_mul_eq_one_right (by rwa [IsUnit.unit_spec, mul_comm])])
  refine ⟨v, ?_⟩
  ext E
  have a := h₁ E
  have b := h₂ E
  rw [PrimeDivisor.ord_inv] at b
  change D₁ E - D₂ E = E.ord v
  change -D₂ E ≤ E.ord v - D₁ E at a
  change -D₁ E ≤ -E.ord v - D₂ E at b
  omega

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Restriction to the open subscheme `⊤` reflects isomorphisms of `𝒪_X`-modules: if
`M|_U ≅ N|_U` for the open `U = X`, then `M ≅ N`. -/
theorem nonempty_iso_of_restrict_iso {M N : X.Modules} {U : X.Opens} (hU : U = ⊤)
    (e : M.restrict U.ι ≅ N.restrict U.ι) : Nonempty (M ≅ N) := by
  subst hU
  let j := X.topIso.inv
  have hj : j ≫ (⊤ : X.Opens).ι = 𝟙 X := Scheme.toIso_inv_ι X
  let eP (P : X.Modules) : P ≅ (P.restrict (⊤ : X.Opens).ι).restrict j :=
    (Scheme.Modules.restrictFunctorId.app P).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hj.symm).app P ≪≫
      (Scheme.Modules.restrictFunctorComp j (⊤ : X.Opens).ι).app P
  exact ⟨eP M ≪≫ (Scheme.Modules.restrictFunctor j).mapIso e ≪≫ (eP N).symm⟩

/-- **Canonical divisors of a smooth integral scheme are linearly equivalent.** If the smooth
locus of `f : X ⟶ S` is all of `X`, two canonical divisors `K`, `K'` have
`𝒪_X(K) ≅ ω_X ≅ 𝒪_X(K')`, hence `K ∼ K'`
(`MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso`). -/
theorem linearlyEquivalent_of_isCanonicalDivisor [IsIntegral X] [CompactSpace X] {k : Type u}
    [Field k] {f : X ⟶ Spec (.of k)} (hf : IsSmoothScheme f) {n : ℕ} {K K' : Divisor X}
    (hK : K.IsCanonicalDivisor f n) (hK' : K'.IsCanonicalDivisor f n) :
    K.LinearlyEquivalent K' :=
  linearlyEquivalent_of_divisorialSheaf_iso
    (nonempty_iso_of_restrict_iso hf (hK.iso ≪≫ hK'.iso.symm)).some

end MMP.Flips
