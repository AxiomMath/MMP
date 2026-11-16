module
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.Restriction
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformIdeal
public import MMP.Analysis.Complex.AvoidanceChart
public import MMP.AlgebraicGeometry.Resolution.ZariskiSequenceBasic
public import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreChartCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Noetherian

/-!
# Restriction of transforms, analytic avoidance, Stein factorization and valuation charts

This file collects several independent foundational results.

* **Restriction of twisted pull-backs and birational transforms** (Kollár 3.58, 3.62). Let
  `j : H → X` be a morphism, `Z ⊆ X` a closed subscheme, `π : B_ZX → X`, `π_H : B_{j⁻¹Z}H → H`
  the blow-ups and `ι : B_{j⁻¹Z}H → B_ZX` the canonical lift of `j`. Quotients by effective
  Cartier divisors commute with inverse images along `ι`; hence twisted pull-backs
  `𝒪(∑ a_jF_j)·π^*I` and birational transforms of marked ideals commute with restriction to
  `H`.
* **Analytic avoidance charts.** If `B ⊆ ℂⁿ` is an open ball and `A ⊆ B` is the common zero
  locus of finitely many holomorphic functions on `B`, not all identically zero, then `B \ A` is
  dense in `B` and path connected. The second statement goes through the one-variable fact that
  `0` and `1` are joined in `Ω \ {g = 0}` when `g` is holomorphic on a disc `Ω ⊇ [0, 1]` with
  `g(0)g(1) ≠ 0`.
* **Stein factorization.** A proper morphism `h : X → Z` of Noetherian schemes factors as
  `X → Z' → Z`, `Z' = Spec_Z(h_* 𝒪_X)`, and the first map induces a bijection from the connected
  components of `h⁻¹(z)` onto the finite fibre `s⁻¹(z)`.
* **The chart selected by a valuation.** For the blow-up `X'` of an integral variety `X` along
  the closure of a non-generic point `x`, a valuation ring `R` of `k(X)` dominating `𝒪_{X,x}`
  lifts to `X'`, and the local ring at the image of its closed point is the localization of the
  chart ring `𝒪_{X,x}[z_j / z_{i₀}]` of a generator `z_{i₀}` of least valuation.
* **Embedding dimension.** The Krull dimension of a Noetherian local ring is at most the
  dimension of its cotangent space.

## Main results

* `MMP.Resolution.Kollar.comap_canonicalLift_idealColon_exceptionalDivisorIdeal`: twisted
  pull-backs restrict to twisted pull-backs.
* `MMP.Resolution.Kollar.birationalTransform_comap_eq_comap_canonicalLift`: birational transforms
  of marked ideals commute with restriction.
* `MMP.Fourfold.AnalyticAvoidanceChart.ball_subset_closure_ball_diff_excludedSet`: `B \ A` is
  dense in `B`.
* `MMP.Analytic.joinedIn_ball_diff_zeros_of_segment_subset`: `0` and `1` are joined in a disc
  avoiding the zeros of a holomorphic function nonzero at both.
* `MMP.Fourfold.AnalyticAvoidanceChart.isPathConnected_ball_diff_excludedSet`: `B \ A` is path
  connected.
* `MMP.exists_isSteinFactorization_and_connectedComponents_equiv`: Stein factorization and the
  bijection `π₀(h⁻¹(z)) ≃ s⁻¹(z)`.
* `MMP.Mori.blowUp_vanishingIdeal_closure_valuation_chart`: the blow-up at a point closure and
  the chart selected by a valuation.
* `MMP.ringKrullDim_le_finrank_cotangentSpace`: `dim R ≤ dim_κ 𝔪 / 𝔪²`.

## Implementation notes

* The twist `𝒪(∑_j a_jF_j)·π^*I` is the ideal quotient `(π^*I : 𝒪(-∑_j a_jF_j))`, with
  `𝒪(-∑_j a_jF_j) = MMP.Resolution.exceptionalDivisorIdeal`; the coefficients are a function `a`
  on subsets of `X`, read on a component `W'` of `j⁻¹Z` as `a (j '' W')`. The source's
  hypotheses that `H` have pure codimension one, that `Z ⊊ H`, and that `I`, `I|_H` be nonzero
  on every component are not needed and are dropped. For marked ideals, `ord_Z I ≥ m` is
  replaced by its consequence `π^*I ⊆ (π^*I_Z)^m`, and `j`, `Z` are arbitrary. Restriction of
  an ideal sheaf along a morphism is `Scheme.IdealSheafData.comap`.
* The source proves density by restricting to complex lines and applying the one-variable
  identity theorem; Mathlib's identity theorem holds in any normed space and is applied on the
  ball directly. The source joins `0` to `1` along the segment with semicircular detours around
  the finitely many zeros on it; here the zeros of `g` in the disc are discrete, hence
  countable, and the complement of a countable subset of a disc is path connected
  (`Set.Countable.isPathConnected_compl_of_one_lt_rank`).
* The Stein factorization is recorded by `Stacks.SteinFactorization.IsSteinFactorization`, which
  gives geometrically connected fibres. Fibres are set-theoretic preimages with the subspace
  topology.
* "Of finite type over `k₀`" is `LocallyOfFiniteType sX` with `QuasiCompact sX`. The local ring
  at the image of the closed point is identified with a subring of `k(X)` through the local
  homomorphism to `R` induced by the lift, which avoids identifying `k(X')` with `k(X)`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.58, 3.62]
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 17
* [Stacks, Tag 03H0]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, proof of Lemma 2.45]
* [Matsumura, *Commutative Ring Theory*, Theorem 13.4 and §14]
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-! ### Restriction of twisted pull-backs and birational transforms -/

namespace MMP.Resolution.Kollar

open Stacks.Divisors

/-- The preimage of an irreducible set contained in the range of an inducing map is
irreducible. -/
private theorem isIrreducible_preimage_of_subset_range {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hf : Topology.IsInducing f) {T : Set B}
    (hT : IsIrreducible T) (hTr : T ⊆ Set.range f) : IsIrreducible (f ⁻¹' T) := by
  obtain ⟨⟨b, hb⟩, hpre⟩ := hT
  obtain ⟨a, rfl⟩ := hTr hb
  refine ⟨⟨a, hb⟩, fun u v hu hv ⟨x, hxT, hxu⟩ ⟨y, hyT, hyv⟩ => ?_⟩
  obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.1 hu
  obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.1 hv
  obtain ⟨z, hzT, hzu, hzv⟩ := hpre u' v' hu' hv' ⟨f x, hxT, hxu⟩ ⟨f y, hyT, hyv⟩
  obtain ⟨w, rfl⟩ := hTr hzT
  exact ⟨w, hzT, hzu, hzv⟩

/-- Under an inducing map `f`, an irreducible component of `f⁻¹ D` maps to an irreducible
component of `D`, when `D` lies in the range of `f`. -/
private theorem image_mem_componentsOf {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (hf : Topology.IsInducing f) {D : Set B} (hD : D ⊆ Set.range f) {W : Set A}
    (hW : W ∈ componentsOf (f ⁻¹' D)) : f '' W ∈ componentsOf D := by
  refine ⟨⟨hW.1.1.image f hf.continuous.continuousOn, Set.image_subset_iff.2 hW.1.2⟩, ?_⟩
  rintro T ⟨hT, hTD⟩ hle
  have hpre : f ⁻¹' T ⊆ W :=
    hW.2 ⟨isIrreducible_preimage_of_subset_range hf hT (hTD.trans hD),
      Set.preimage_mono hTD⟩ (Set.image_subset_iff.1 hle)
  intro b hb
  obtain ⟨a, rfl⟩ := hD (hTD hb)
  exact ⟨a, hpre hb, rfl⟩

/-- Stalk of `𝒪(-∑_j b_jF_j)` at a point `y` over a component `W` of `Z`: it is
`(π^*I_Z)_y^{b_W}`. -/
private theorem stalk_exceptionalDivisorIdeal_eq_of_mem {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (b : componentsOf (Z.support : Set X) → ℕ) (y : blowUp Z) (W : Set X)
    (hW : W ∈ componentsOf (Z.support : Set X)) (hy : blowUpToBase Z y ∈ W) :
    IdealSheafData.stalk (exceptionalDivisorIdeal Z b) y =
      IdealSheafData.stalk (Z.comap (blowUpToBase Z)) y ^ b ⟨W, hW⟩ := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  let := Fintype.ofFinite (componentsOf (Z.support : Set X))
  set x := blowUpToBase Z y
  have hx : x ∈ (Z.support : Set X) := hW.1.2 hy
  obtain ⟨W0, hW0, hxW0, huniq, hstalk, -⟩ := exists_component_through sX hX Z hZ ⊥ x hx
  obtain rfl : W = W0 := huniq W hW hy
  have hD : IdealSheafData.stalk (exceptionalDivisorIdeal Z b) y =
      ∏ W : componentsOf (Z.support : Set X), Ideal.map ((blowUpToBase Z).stalkMap y).hom
        (IdealSheafData.stalk (componentsFamily (Z.support : Set X) W) x) ^ b W := by
    unfold exceptionalDivisorIdeal
    rw [finprod_eq_prod_of_fintype, stalk_prod]
    refine Finset.prod_congr rfl fun W _ => ?_
    rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
  rw [hD, Finset.prod_eq_single (⟨W, hW⟩ : componentsOf (Z.support : Set X))]
  · rw [hstalk, ← IdealSheafData.stalk_comap]
  · intro W' _ hne
    have : x ∉ (W' : Set X) := fun hxW => hne (Subtype.ext (huniq W' W'.2 hxW))
    rw [stalk_componentsFamily_eq_top Z W'.2 this, Ideal.map_top, ← Ideal.one_eq_top, one_pow]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- If `Z ⊆ H`, the subscheme `j⁻¹Z` of `H` is smooth over `k` when `Z` is. -/
private theorem isSmoothScheme_comap_subschemeι {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (H Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hHZ : H ≤ Z) :
    MMP.Mori.IsSmoothScheme ((Z.comap H.subschemeι).subschemeι ≫ H.subschemeι ≫ sX) := by
  have hsq : IsPullback (Scheme.IdealSheafData.inclusion hHZ) (𝟙 _) H.subschemeι
      Z.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp [Scheme.IdealSheafData.inclusion_subschemeι]⟩
  have hiso : IsIso (pullback.snd H.subschemeι Z.subschemeι) := by
    have : hsq.isoPullback.hom ≫ pullback.snd _ _ = 𝟙 _ := hsq.isoPullback_hom_snd
    rw [(Iso.hom_comp_eq_id _).1 this]
    infer_instance
  have heq : (Z.comap H.subschemeι).subschemeι ≫ H.subschemeι ≫ sX =
      ((Z.comapIso H.subschemeι).hom ≫ pullback.snd _ _) ≫ Z.subschemeι ≫ sX := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc,
      Category.assoc]
  rw [heq]
  have : LocallyOfFinitePresentation (Z.subschemeι ≫ sX) :=
    instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  have : LocallyOfFinitePresentation (((Z.comapIso H.subschemeι).hom ≫ pullback.snd _ _) ≫
      Z.subschemeι ≫ sX) :=
    instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  rw [MMP.Mori.isSmoothScheme_iff] at hZ ⊢
  infer_instance

/-- `𝒪_{B_ZX}(-∑_j a_jF_j)` restricts along the canonical lift `ι : B_ZH → B_ZX` to
`𝒪_{B_ZH}(-∑_j a_jF_{H,j})`. -/
private theorem comap_canonicalLift_exceptionalDivisorIdeal {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (H Z : X.IdealSheafData)
    (hH : MMP.Mori.IsSmoothScheme (H.subschemeι ≫ sX))
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hHZ : H ≤ Z) (a : Set X → ℕ) :
    (exceptionalDivisorIdeal Z fun W => a W.1).comap (canonicalLift H.subschemeι Z) =
      exceptionalDivisorIdeal (Z.comap H.subschemeι) fun W => a (H.subschemeι '' W.1) := by
  set j := H.subschemeι with hjdef
  set ι := canonicalLift j Z
  have hZH := isSmoothScheme_comap_subschemeι sX H Z hZ hHZ
  have hrange : (Z.support : Set X) ⊆ Set.range j := by
    rw [hjdef, Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.support_antitone hHZ
  have hpt : ∀ y, blowUpToBase Z (ι y) = j (blowUpToBase (Z.comap j) y) := fun y => by
    rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
  refine IdealSheafData.eq_of_stalk_eq _ _ fun y => ?_
  rw [IdealSheafData.stalk_comap]
  by_cases hx : blowUpToBase (Z.comap j) y ∈ ((Z.comap j).support : Set H.subscheme)
  · obtain ⟨W', hW', hxW', -⟩ :=
      exists_component_through (j ≫ sX) hH (Z.comap j) hZH ⊥ _ hx
    have hsupp : ((Z.comap j).support : Set H.subscheme) = j ⁻¹' (Z.support : Set X) := by
      rw [Scheme.IdealSheafData.support_comap]
      rfl
    have hW : j '' W' ∈ componentsOf (Z.support : Set X) := by
      rw [hsupp] at hW'
      exact image_mem_componentsOf j.isEmbedding.isInducing hrange hW'
    rw [stalk_exceptionalDivisorIdeal_eq_of_mem (j ≫ sX) hH (Z.comap j) hZH _ y W' hW' hxW',
      stalk_exceptionalDivisorIdeal_eq_of_mem sX hX Z hZ _ (ι y) (j '' W') hW
        (by rw [hpt]; exact ⟨_, hxW', rfl⟩),
      Ideal.map_pow, ← IdealSheafData.stalk_comap, comap_canonicalLift_comap_blowUpToBase]
  · have htop : IdealSheafData.stalk ((Z.comap j).comap (blowUpToBase (Z.comap j))) y = ⊤ := by
      rw [IdealSheafData.stalk_comap,
        (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hx, Ideal.map_top]
    obtain ⟨n, hn, -, -⟩ := exists_stalk_exceptionalDivisorIdeal_eq sX hX Z hZ
      (fun W => a W.1) (ι y)
    obtain ⟨n', hn', -, -⟩ := exists_stalk_exceptionalDivisorIdeal_eq (j ≫ sX) hH (Z.comap j)
      hZH (fun W => a (j '' W.1)) y
    rw [hn, hn', Ideal.map_pow, ← IdealSheafData.stalk_comap,
      comap_canonicalLift_comap_blowUpToBase, htop, ← Ideal.one_eq_top, one_pow, one_pow]

/-- For an effective Cartier divisor `B`, `idealColon A B` is the ideal-sheaf quotient
`Scheme.IdealSheafData.colon`. -/
private theorem idealColon_eq_colon {X : Scheme.{u}} (A B : X.IdealSheafData)
    (hB : IsEffectiveCartierDivisor B) :
    idealColon A B = A.colon B (fg_ideal_of_isEffectiveCartierDivisor B hB) :=
  Scheme.IdealSheafData.ofIdeals_ideal (A.colon B _)

/-- Dividing a product by an effective Cartier divisor: `(D · J : D) = J`. -/
private theorem idealColon_mul_cancel_left {X : Scheme.{u}} (D J : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) : idealColon (D * J) D = J := by
  rw [idealColon_eq_colon _ _ hD]
  choose U hU hxU b hb hgen using
    fun x : X => exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D hD x
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun x : X => (⟨U x, hU x⟩ : X.affineOpens))
    (top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hxU z⟩) fun x => ?_
  rw [Scheme.IdealSheafData.ideal_colon, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hgen x]
  ext d
  rw [Ideal.colon_span, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton_mul]
  exact ⟨fun ⟨z, hz, hzd⟩ => ((hb x).left (show b x * d = b x * z by rw [hzd]; ring)) ▸ hz,
    fun hd => ⟨d, hd, mul_comm _ _⟩⟩

/-- The quotient by an effective Cartier divisor `D ⊇ A` commutes with pulling back along any
morphism `f` for which `f⁻¹D` is again an effective Cartier divisor. -/
private theorem idealColon_comap {X Y : Scheme.{u}} (f : Y ⟶ X) {A D : X.IdealSheafData}
    (hD : IsEffectiveCartierDivisor D) (hfD : IsEffectiveCartierDivisor (D.comap f))
    (hAD : A ≤ D) : idealColon (A.comap f) (D.comap f) = (idealColon A D).comap f := by
  conv_lhs => rw [← mul_colon_eq_of_isEffectiveCartierDivisor D A hD hAD,
    Stacks.IdealSheaf.comap_mul, idealColon_mul_cancel_left _ _ hfD]
  rw [idealColon_eq_colon _ _ hD]

/-- **Twisted pull-backs restrict to twisted pull-backs** (Kollár (3.58.2), proof of 3.62). Let
`X` be smooth over `k`, `H ⊆ X` a smooth closed subscheme with inclusion `j`, `Z ⊆ H` a smooth
closed subscheme, `π : B_ZX → X`, `π_H : B_{j⁻¹Z}H → H` the blow-ups and `ι` the canonical lift
of `j`. If `a_j ≤ ord_{Z_j} I` along every irreducible component `Z_j` of `Z`, then
`(𝒪_{B_ZX}(∑_j a_jF_j)·π^*I)·𝒪_{B_ZH} = 𝒪_{B_ZH}(∑_j a_jF_{H,j})·π_H^*(I|_H)`. -/
@[mmp "lem_kr3c_twisted_pullback_restricts"]
public theorem comap_canonicalLift_idealColon_exceptionalDivisorIdeal {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (H Z : X.IdealSheafData)
    (hH : MMP.Mori.IsSmoothScheme (H.subschemeι ≫ sX))
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hHZ : H ≤ Z)
    (I : X.IdealSheafData) (a : Set X → ℕ)
    (ha : ∀ W (hW : W ∈ componentsOf (Z.support : Set X)), (a W : ℕ∞) ≤ orderAlong I hW.1.1) :
    (idealColon (I.comap (blowUpToBase Z))
        (exceptionalDivisorIdeal Z fun W => a W.1)).comap (canonicalLift H.subschemeι Z) =
      idealColon ((I.comap H.subschemeι).comap (blowUpToBase (Z.comap H.subschemeι)))
        (exceptionalDivisorIdeal (Z.comap H.subschemeι) fun W => a (H.subschemeι '' W.1)) := by
  have hkey := comap_canonicalLift_exceptionalDivisorIdeal sX hX H Z hH hZ hHZ a
  have h := idealColon_comap (canonicalLift H.subschemeι Z)
    (isEffectiveCartierDivisor_exceptionalDivisorIdeal sX hX Z hZ _)
    (hkey ▸ isEffectiveCartierDivisor_exceptionalDivisorIdeal (H.subschemeι ≫ sX) hH _
      (isSmoothScheme_comap_subschemeι sX H Z hZ hHZ) _)
    (comap_le_exceptionalDivisorIdeal sX hX Z hZ I _ fun W => ha W.1 W.2)
  rw [hkey, comap_canonicalLift_comap_blowUpToBase] at h
  exact h.symm

/-- **Kollár 3.62.** Let `j : H → X` be a morphism, `Z ⊆ X` a closed subscheme, `π : B_ZX → X`,
`π_H : B_{j⁻¹Z}H → H` the blow-ups and `ι : B_{j⁻¹Z}H → B_ZX` the canonical lift of `j`. For a
marked ideal `(I, m)` on `X` with `π^*I ⊆ (π^*I_Z)^m` (which holds when `ord_Z I ≥ m` on a
smooth `X`), the birational transform of `(I|_H, m)` along `π_H` is the restriction along `ι` of
the birational transform of `(I, m)` along `π`:
`𝒪_{B_ZH}(mF_H)·π_H^*(I|_H) = (𝒪_{B_ZX}(mF)·π^*I)·𝒪_{B_ZH}`, with marking `m`. -/
@[mmp "lem_kr3c_marked_transform_commutes_restriction"]
public theorem birationalTransform_comap_eq_comap_canonicalLift {X H : Scheme.{u}} (j : H ⟶ X)
    (Z : X.IdealSheafData) (a : MarkedIdeal X)
    (ha : a.I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ a.m) :
    (⟨a.I.comap j, a.m⟩ : MarkedIdeal H).birationalTransform (Z.comap j) =
      ⟨(a.birationalTransform Z).I.comap (canonicalLift j Z), a.m⟩ := by
  have hEH : IsEffectiveCartierDivisor ((Z.comap (blowUpToBase Z) ^ a.m).comap
      (canonicalLift j Z)) := by
    rw [Stacks.IdealSheaf.comap_pow, comap_canonicalLift_comap_blowUpToBase]
    exact isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.comap j)) a.m
  have h := idealColon_comap (canonicalLift j Z) (isEffectiveCartierDivisor_pow
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z) a.m) hEH ha
  rw [Stacks.IdealSheaf.comap_pow, comap_canonicalLift_comap_blowUpToBase,
    comap_canonicalLift_comap_blowUpToBase] at h
  exact congrArg (MarkedIdeal.mk · a.m) h

end MMP.Resolution.Kollar

/-! ### Analytic avoidance charts -/

namespace MMP.Fourfold.AnalyticAvoidanceChart

open Topology

/-- A chart function that is nonzero somewhere on the ball is nonzero at points arbitrarily close
to any point of the ball. -/
private lemma frequently_ne_zero {n : ℕ} (C : AnalyticAvoidanceChart n) {i : Fin C.r}
    {a x : EuclideanSpace ℂ (Fin n)} (ha : a ∈ C.ball) (hfa : C.f i a ≠ 0) (hx : x ∈ C.ball) :
    ∃ᶠ y in 𝓝 x, C.f i y ≠ 0 := fun hev =>
  hfa <| (C.analyticOnNhd i).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball C.center C.radius).isPreconnected hx (hev.mono fun _ => not_not.mp) ha

/-- The complement of the excluded subset of an analytic avoidance chart is dense in its ball. -/
@[mmp "lem_mmp_avoidance_chart_dense"]
public theorem ball_subset_closure_ball_diff_excludedSet {n : ℕ} (C : AnalyticAvoidanceChart n) :
    C.ball ⊆ closure (C.ball \ C.excludedSet) := by
  intro x hx
  obtain ⟨i, a, ha, hfa⟩ := C.exists_ne_zero
  exact mem_closure_iff_frequently.mpr <|
    ((frequently_ne_zero C ha hfa hx).and_eventually (C.isOpen_ball.mem_nhds hx)).mono
      fun y ⟨hne, hy⟩ => ⟨hy, fun h => hne (h.2 i)⟩

end MMP.Fourfold.AnalyticAvoidanceChart

namespace MMP.Analytic

/-- A function holomorphic on a disc and nonzero at one of its points has countably many zeros
in the disc. -/
private lemma countable_zeros_inter_ball {c : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball c r)) {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball c r)
    (hgz₀ : g z₀ ≠ 0) : ({z | g z = 0} ∩ Metric.ball c r).Countable := by
  have hcod := mem_codiscreteWithin.mp <|
    (hg.analyticOnNhd Metric.isOpen_ball).preimage_zero_mem_codiscreteWithin hgz₀ hz₀
      ((convex_ball c r).isConnected ⟨z₀, hz₀⟩)
  have : DiscreteTopology ↥(Metric.ball c r \ g ⁻¹' {0}ᶜ) :=
    discreteTopology_subtype_iff.2 fun x hx => (hcod x hx.1).eq_bot
  exact (Set.countable_coe_iff.mp (countable_of_Lindelof_of_discrete
    (X := ↥(Metric.ball c r \ g ⁻¹' {0}ᶜ)))).mono fun z hz => by simp_all

/-- Removing a countable set from an open disc in `ℂ` leaves a path-connected set. -/
private lemma isPathConnected_ball_diff_of_countable {c : ℂ} {r : ℝ} (hr : 0 < r) {S : Set ℂ}
    (hS : S.Countable) : IsPathConnected (Metric.ball c r \ S) := by
  set e := OpenPartialHomeomorph.univBall c r
  have htgt : e.target = Metric.ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hpc := Set.Countable.isPathConnected_compl_of_one_lt_rank
    (by simp [Complex.rank_real_complex])
    (hS.preimage_of_injOn (f := e) (e.injOn.mono (by simp [e])))
  convert hpc.image (OpenPartialHomeomorph.continuous_univBall c r) using 1
  ext z
  constructor
  · rintro ⟨hz, hzS⟩
    exact ⟨e.symm z, by simpa [e.right_inv (htgt ▸ hz)] using hzS, e.right_inv (htgt ▸ hz)⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨htgt ▸ e.map_source (by simp [e]), hw⟩

/-- If an open disc contains the segment `[0, 1]` and `g` is holomorphic on it with
`g 0 * g 1 ≠ 0`, then `0` and `1` are joined by a path in the disc avoiding the zeros of `g`. -/
@[mmp "lem_mmp_holomorphic_segment_detours"]
public theorem joinedIn_ball_diff_zeros_of_segment_subset {c : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hseg : segment ℝ (0 : ℂ) 1 ⊆ Metric.ball c r)
    (hg : DifferentiableOn ℂ g (Metric.ball c r)) (h01 : g 0 * g 1 ≠ 0) :
    JoinedIn (Metric.ball c r \ {z | g z = 0}) 0 1 := by
  have h0 := hseg (left_mem_segment ℝ 0 1)
  have hpc := isPathConnected_ball_diff_of_countable (c := c) (Metric.pos_of_mem_ball h0)
    (countable_zeros_inter_ball hg h0 (left_ne_zero_of_mul h01))
  rw [Set.sdiff_inter_self_eq_sdiff] at hpc
  exact hpc.joinedIn 0 ⟨h0, left_ne_zero_of_mul h01⟩ 1
    ⟨hseg (right_mem_segment ℝ 0 1), right_ne_zero_of_mul h01⟩

end MMP.Analytic

namespace MMP.Fourfold.AnalyticAvoidanceChart

/-- A complex line `z ↦ a + z • v` (with `v ≠ 0`) through a point `a` of an open ball meets the
ball in an open disc: the preimage of the ball is a ball in `ℂ`. -/
private lemma exists_ball_forall_mem_iff_add_smul_mem_ball {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {a v c : E} {R : ℝ} (hv : v ≠ 0) (ha : a ∈ Metric.ball c R) :
    ∃ z₀ : ℂ, ∃ ρ : ℝ, ∀ z : ℂ, z ∈ Metric.ball z₀ ρ ↔ a + z • v ∈ Metric.ball c R := by
  set w := a - c
  have hvv : inner ℂ v v ≠ 0 := inner_self_ne_zero.2 hv
  set z₀ : ℂ := -(inner ℂ v w) / inner ℂ v v
  set u := w + z₀ • v
  have hvu : inner ℂ v u = 0 := by
    simp only [u, inner_add_right, inner_smul_right, z₀]
    rw [div_mul_cancel₀ _ hvv]
    ring
  have hkey : ∀ z : ℂ, ‖w + z • v‖ ^ 2 = ‖u‖ ^ 2 + ‖z - z₀‖ ^ 2 * ‖v‖ ^ 2 := by
    intro z
    have h1 : w + z • v = u + (z - z₀) • v := by
      simp only [u, sub_smul]
      abel
    have h2 : inner ℂ u ((z - z₀) • v) = 0 := by
      rw [inner_smul_right, ← inner_conj_symm, hvu]
      simp
    rw [h1, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h2, norm_smul]
    ring
  have hu : ‖u‖ ^ 2 < R ^ 2 := by
    have h0 := hkey 0
    rw [zero_smul, add_zero] at h0
    have hw : ‖w‖ < R := by simpa [w, dist_eq_norm] using ha
    nlinarith [norm_nonneg w, norm_nonneg (0 - z₀), norm_nonneg v]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine ⟨z₀, √(R ^ 2 - ‖u‖ ^ 2) / ‖v‖, fun z => ?_⟩
  have hR : 0 < R := Metric.pos_of_mem_ball ha
  rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, lt_div_iff₀ hvpos,
    Real.lt_sqrt (by positivity), show a + z • v - c = w + z • v by simp only [w]; abel,
    ← sq_lt_sq₀ (norm_nonneg _) hR.le, hkey z, mul_pow]
  constructor <;> intro h <;> linarith

/-- `p + c * q` vanishes for at most one `c` when `(p, q) ≠ 0`. -/
private lemma add_mul_ne_zero_of_ne {p q c : ℂ} (hpq : p ≠ 0 ∨ q ≠ 0) (hc : c ≠ -p / q) :
    p + c * q ≠ 0 := by
  intro h
  rcases eq_or_ne q 0 with hq | hq
  · simp_all
  · exact hc (by field_simp; linear_combination h)

/-- Two nonzero vectors `(p₁, q₁)`, `(p₂, q₂)` of `ℂ²` admit a common `c` with
`p₁ + c * q₁ ≠ 0` and `p₂ + c * q₂ ≠ 0`. -/
private lemma exists_add_mul_ne_zero {p₁ q₁ p₂ q₂ : ℂ} (h₁ : p₁ ≠ 0 ∨ q₁ ≠ 0)
    (h₂ : p₂ ≠ 0 ∨ q₂ ≠ 0) : ∃ c : ℂ, p₁ + c * q₁ ≠ 0 ∧ p₂ + c * q₂ ≠ 0 := by
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({-p₁ / q₁, -p₂ / q₂} : Finset ℂ)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, add_mul_ne_zero_of_ne h₁ hc.1, add_mul_ne_zero_of_ne h₂ hc.2⟩

/-- The complement of the excluded subset of an analytic avoidance chart is path connected: any
two of its points are joined by a path inside it. -/
@[mmp "lem_mmp_avoidance_chart_paths"]
public theorem isPathConnected_ball_diff_excludedSet {n : ℕ} (C : AnalyticAvoidanceChart n) :
    IsPathConnected (C.ball \ C.excludedSet) := by
  refine isPathConnected_iff.2 ⟨C.exists_mem_ball_notMem_excludedSet, fun a ha b hb => ?_⟩
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  have hnot : ∀ x ∈ C.ball \ C.excludedSet, ∃ i, C.f i x ≠ 0 := fun x hx => by
    simpa [AnalyticAvoidanceChart.mem_excludedSet, hx.1] using hx.2
  obtain ⟨j, hj⟩ := hnot a ha
  obtain ⟨k, hk⟩ := hnot b hb
  obtain ⟨z₀, ρ, hρ⟩ :=
    exists_ball_forall_mem_iff_add_smul_mem_ball (c := C.center) (R := C.radius)
      (sub_ne_zero.2 hab.symm) ha.1
  set L : ℂ → EuclideanSpace ℂ (Fin n) := fun z => a + z • (b - a)
  have hL0 : L 0 = a := by simp [L]
  have hL1 : L 1 = b := by simp [L]
  have hLmaps : Set.MapsTo L (Metric.ball z₀ ρ) C.ball := fun z hz => (hρ z).1 hz
  obtain ⟨c, hca, hcb⟩ := exists_add_mul_ne_zero (Or.inl hj) (Or.inr hk)
  set h : ℂ → ℂ := fun z => C.f j (L z) + c * C.f k (L z)
  have hLan : AnalyticOnNhd ℂ L (Metric.ball z₀ ρ) := fun z _ => by fun_prop
  have hhol : DifferentiableOn ℂ h (Metric.ball z₀ ρ) :=
    (((C.analyticOnNhd j).comp hLan hLmaps).add
      (analyticOnNhd_const.mul ((C.analyticOnNhd k).comp hLan hLmaps))).differentiableOn
  have hseg : segment ℝ (0 : ℂ) 1 ⊆ Metric.ball z₀ ρ :=
    (convex_ball z₀ ρ).segment_subset
      ((hρ 0).2 (by simpa [AnalyticAvoidanceChart.ball] using ha.1))
      ((hρ 1).2 (by simpa [AnalyticAvoidanceChart.ball] using hb.1))
  have hJ := (MMP.Analytic.joinedIn_ball_diff_zeros_of_segment_subset hseg hhol
    (mul_ne_zero (by simpa [h, hL0] using hca) (by simpa [h, hL1] using hcb))).map
    (f := L) (by fun_prop)
  rw [hL0, hL1] at hJ
  refine hJ.mono ?_
  rintro _ ⟨z, ⟨hz, hz0⟩, rfl⟩
  exact ⟨hLmaps hz, fun hA => hz0 (by simp [h, hA.2 j, hA.2 k])⟩

end MMP.Fourfold.AnalyticAvoidanceChart

/-! ### Stein factorization and connected components of fibres -/

namespace MMP

/-- A continuous surjection onto a discrete space whose fibres are preconnected induces an
equivalence from the connected components of the source onto the target. -/
private theorem exists_connectedComponents_equiv {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [DiscreteTopology B] {φ : A → B} (hφ : Continuous φ)
    (hsurj : Function.Surjective φ) (hconn : ∀ b, _root_.IsPreconnected (φ ⁻¹' {b})) :
    ∃ e : ConnectedComponents A ≃ B, ∀ a, e (ConnectedComponents.mk a) = φ a := by
  refine ⟨Equiv.ofBijective hφ.connectedComponentsLift ⟨fun p q hpq => ?_, fun b => ?_⟩,
    fun _ => rfl⟩
  · obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe p
    obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe q
    exact ConnectedComponents.coe_eq_coe'.mpr
      ((hconn (φ b)).subset_connectedComponent rfl hpq)
  · obtain ⟨a, rfl⟩ := hsurj b
    exact ⟨ConnectedComponents.mk a, rfl⟩

/-- If `f = s ∘ g` with `g` continuous with nonempty connected fibres and the fibre `s⁻¹(z)`
discrete, then `g` induces an equivalence from the connected components of `f⁻¹(z)` onto
`s⁻¹(z)`. -/
private theorem exists_connectedComponents_fibre_equiv {A B C : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → C} {g : A → B} {s : B → C} (hg : Continuous g)
    (hfg : ∀ a, s (g a) = f a) (hfib : ∀ b, _root_.IsConnected (g ⁻¹' {b})) (z : C)
    [DiscreteTopology (s ⁻¹' {z})] :
    ∃ e : ConnectedComponents (f ⁻¹' {z}) ≃ s ⁻¹' {z},
      ∀ a, (e (ConnectedComponents.mk a) : B) = g a := by
  have hsub {b : B} (hb : s b = z) : g ⁻¹' {b} ⊆ f ⁻¹' {z} := fun a ha => by
    simp_all [← hfg]
  let φ : f ⁻¹' {z} → s ⁻¹' {z} := fun a => ⟨g a, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hfg]
    exact a.2⟩
  have hφ : ∀ b : s ⁻¹' {z}, φ ⁻¹' {b} = Subtype.val ⁻¹' (g ⁻¹' {b.1}) := fun b => by
    ext
    simp [φ, Subtype.ext_iff]
  obtain ⟨e, he⟩ := exists_connectedComponents_equiv (φ := φ)
    ((hg.comp continuous_subtype_val).subtype_mk _)
    (fun ⟨b, hb⟩ => by
      obtain ⟨a, ha⟩ := (hfib b).nonempty
      exact ⟨⟨a, hsub hb ha⟩, Subtype.ext ha⟩)
    (fun b => by
      rw [hφ, ← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        Set.inter_eq_right.mpr (hsub b.2)]
      exact (hfib b).isPreconnected)
  exact ⟨e, fun a => by rw [he]⟩

/-- **Stein factorization and the fibre-component bijection.** A proper morphism `h : X ⟶ Z` of
Noetherian schemes factors as `h = h' ≫ s` with `(h', s)` a Stein factorization
(`Z' = Spec_Z(h_* 𝒪_X)`, `h'` proper with `h'_* 𝒪_X = 𝒪_{Z'}` and geometrically connected fibres,
`s` finite), and for each `z : Z` the map `h'` induces a bijection from the connected
components of `h ⁻¹' {z}` onto `s ⁻¹' {z}`. -/
@[mmp "lem_mmp_foundation_fa17_general_stein_factorization"]
public theorem exists_isSteinFactorization_and_connectedComponents_equiv
    {X Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z] (h : X ⟶ Z) [IsProper h] :
    ∃ (Z' : Scheme.{u}) (h' : X ⟶ Z') (s : Z' ⟶ Z),
      Nonempty (Stacks.SteinFactorization.IsSteinFactorization h h' s) ∧
      ∀ z : Z, ∃ e : _root_.ConnectedComponents ↥(h ⁻¹' {z}) ≃ ↥(s ⁻¹' {z}),
        ∀ x : ↥(h ⁻¹' {z}), (e (_root_.ConnectedComponents.mk x) : Z') = h' x.1 := by
  have : IsLocallyNoetherian Z := ‹IsNoetherian Z›.toIsLocallyNoetherian
  obtain ⟨Z', h', s, ⟨hS⟩⟩ := Stacks.SteinFactorization.exists_isSteinFactorization h
  have := hS.geometricallyConnected
  have := hS.isFinite
  refine ⟨Z', h', s, ⟨hS⟩, fun z => ?_⟩
  have : DiscreteTopology (s ⁻¹' {z}) := (s.isDiscrete_preimage_singleton z).to_subtype
  exact exists_connectedComponents_fibre_equiv h'.continuous
    (fun x => by rw [← Scheme.Hom.comp_apply, hS.comp]) h'.isConnected_preimage_singleton z

end MMP

/-! ### The blow-up at a point closure and the chart selected by a valuation -/

namespace MMP.Mori

open TopologicalSpace

/-- On an affine scheme, the ideal sheaf of `I ⊆ Γ(X, ⊤)` has `I` as its ideal on `⊤`. -/
private theorem ofIdealTop_ideal_top {X : Scheme.{u}} [IsAffine X] (I : Ideal Γ(X, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top X⟩ = I := by
  simp

/-- The vanishing ideal of the closure of a non-generic point of an integral scheme is nonzero. -/
private theorem vanishingIdeal_closure_ne_bot {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hx : x ≠ genericPoint X) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x}) ≠ ⊥ := by
  intro h
  apply hx
  have hs := congrArg (fun I : X.IdealSheafData => (I.support : Set X)) h
  exact ((genericPoint_spec X).eq (by simpa [IsGenericPoint] using hs)).symm

/-- The maximal ideal of the local ring at a non-generic point of an integral scheme is
nonzero. -/
private theorem maximalIdeal_stalk_ne_bot {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hx : x ≠ genericPoint X) : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≠ ⊥ := by
  intro hm
  apply hx
  obtain ⟨q, hq⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have hq' : q = IsLocalRing.closedPoint _ :=
    PrimeSpectrum.ext ((le_bot_iff.mp (hm ▸ IsLocalRing.le_maximalIdeal q.2.ne_top)).trans hm.symm)
  rw [← hq, hq', Scheme.fromSpecStalk_closedPoint]

/-- The stalk at `x` of the vanishing ideal of the closure of `x` is the maximal ideal of
`𝒪_{X,x}`. -/
private theorem stalk_vanishingIdeal_closure_eq_maximalIdeal {X : Scheme.{u}} (x : X) :
    IdealSheafData.stalk
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let Ua : X.affineOpens := ⟨U, hU⟩
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hpre : (hU.fromSpec : Spec (.of Γ(X, U)) ⟶ X) ⁻¹' ({x} : Set X) =
      ({p} : Set (PrimeSpectrum Γ(X, U))) := by
    ext z
    change hU.fromSpec z = x ↔ z = p
    constructor
    · intro hz
      exact hU.fromSpec.isOpenEmbedding.injective
        (by rwa [hU.fromSpec_primeIdealOf])
    · rintro rfl
      exact hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hcl : (hU.fromSpec : Spec (.of Γ(X, U)) ⟶ X) ⁻¹'
      closure ({x} : Set X) = closure ({p} : Set (PrimeSpectrum Γ(X, U))) := by
    rw [hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous, hpre]
    rfl
  have hvan : PrimeSpectrum.vanishingIdeal
      ((hU.fromSpec : Spec (.of Γ(X, U)) ⟶ X) ⁻¹' closure ({x} : Set X)) = p.asIdeal :=
    (congrArg PrimeSpectrum.vanishingIdeal hcl).trans
      ((PrimeSpectrum.vanishingIdeal_closure ({p} : Set (PrimeSpectrum Γ(X, U)))).trans
        (PrimeSpectrum.vanishingIdeal_singleton p))
  rw [IdealSheafData.stalk_eq_map_germ _ x Ua hxU,
    Scheme.IdealSheafData.vanishingIdeal_ideal]
  change Ideal.map (X.presheaf.germ U x hxU).hom
      (PrimeSpectrum.vanishingIdeal
        ((hU.fromSpec : Spec (.of Γ(X, U)) ⟶ X) ⁻¹' closure ({x} : Set X))) = _
  rw [hvan]
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal (X.presheaf.stalk x)

/-- The inverse image along `Spec 𝒪_{X,x} ⟶ X` of the vanishing ideal of the closure of `x` is
the ideal sheaf of the maximal ideal of `𝒪_{X,x}`. -/
private theorem vanishingIdeal_closure_comap_fromSpecStalk {X : Scheme.{u}} (x : X) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).comap (X.fromSpecStalk x) =
      Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map (Scheme.ΓSpecIso _).inv.hom) := by
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [ideal_comap_fromSpecStalk, Scheme.IdealSheafData.ofIdealTop_ideal,
    stalk_vanishingIdeal_closure_eq_maximalIdeal]
  simp

/-- The charts of a finite generating family of `J(U)` cover the part of the blow-up lying
over the affine open `U`. -/
private theorem iSup_blowUpChartOpen_eq_preimage {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (U : Y.affineOpens) {ι : Type*} [Finite ι] (a : ι → J.ideal U)
    (ha : Ideal.span (Set.range fun j => (a j : Γ(Y, U.1))) = J.ideal U) :
    ⨆ j, (blowUpChartOpen J U (a j)).1 = blowUpToBase J ⁻¹ᵁ U.1 := by
  classical
  have := Fintype.ofFinite ι
  let A : Finset (J.ideal U) := insert 0 (Finset.univ.image a)
  have hspan : Ideal.span ((fun b : J.ideal U => (b : Γ(Y, U.1))) '' (A : Set (J.ideal U))) =
      J.ideal U := by
    simp only [A, Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.image_insert_eq, ZeroMemClass.coe_zero, Ideal.span_insert_zero, ← Set.range_comp]
    exact ha
  rw [← iSup_blowUpChartOpen J U A (Finset.insert_nonempty _ _) hspan]
  refine le_antisymm (iSup_le fun j => ?_) (iSup₂_le fun b hb => ?_)
  · exact le_iSup₂_of_le (a j)
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem a (Finset.mem_univ j))) le_rfl
  rcases Finset.mem_insert.mp hb with rfl | hb
  · intro y hy
    obtain ⟨w, -⟩ : y ∈ (blowUpAffineChart J U 0).opensRange := by
      rwa [← Scheme.Hom.image_top_eq_opensRange]
    exact ((isEmpty_spec_blowUpAffineChartRing_of_eq_zero J U 0 rfl).false w).elim
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    exact le_iSup (fun j => (blowUpChartOpen J U (a j)).1) j

/-- **Valuation rings of the function field lift to a proper blow-up.** If `I ≠ 0` on an
integral scheme `X` and the blow-up `β : Bl_I X ⟶ X` is proper, then for every subring
`𝒪_{X,x} ⊆ R ⊆ k(X)` which is a valuation ring of `k(X)`, the morphism `Spec R ⟶ X` lifts along
`β`. -/
private theorem exists_comp_blowUpToBase_eq_fromSpecOfStalkLE {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) [IsProper (blowUpToBase I)] (x : X)
    (R : ValuationSubring X.functionField)
    (hR : ∀ s : X.presheaf.stalk x, algebraMap _ X.functionField s ∈ R.toSubring) :
    ∃ g : Spec (.of R) ⟶ blowUp I, g ≫ blowUpToBase I = fromSpecOfStalkLE x R.toSubring hR := by
  let U : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  have hη : genericPoint X ∈ U := genericPoint_notMem_supportSet I hI
  have : IsIso (blowUpToBase I ∣_ U) := isIso_blowUp_restrict_compl_support I
  let i₁ : Spec (X.presheaf.stalk (genericPoint X)) ⟶ blowUp I :=
    U.fromSpecStalkOfMem _ hη ≫ inv (blowUpToBase I ∣_ U) ≫ (blowUpToBase I ⁻¹ᵁ U).ι
  have h₁ : i₁ ≫ blowUpToBase I = X.fromSpecStalk (genericPoint X) := by
    simp only [i₁, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence (blowUpToBase I) := by
    have h : @IsProper _ _ (blowUpToBase I) := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq (blowUpToBase I) :=
    { R := R
      domain := inferInstance
      K := X.functionField
      i₁ := i₁
      i₂ := fromSpecOfStalkLE x R.toSubring hR
      commSq := ⟨by
        rw [h₁, fromSpecOfStalkLE, ← Category.assoc, ← Spec.map_comp]
        exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen).symm⟩ }
  obtain ⟨⟨l, -, hl₂⟩⟩ := (hex S).exists_lift
  exact ⟨l, hl₂⟩

/-- A flat preimmersion induces bijections on local rings. -/
private theorem bijective_stalkMap_of_flat_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IsPreimmersion f] (x : X) : Function.Bijective (f.stalkMap x).hom := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (Flat.iff_flat_stalkMap f).mp ‹Flat f› x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
    change IsLocalHom (f.stalkMap x).hom
    infer_instance
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨FaithfulSMul.algebraMap_injective _ _, Scheme.Hom.stalkMap_surjective f x⟩

open IsLocalization in
/-- Let `φ : B → K` be an injective map into a field, `R` a valuation ring of `K` containing
its image, `𝔭 = φ⁻¹(𝔪_R)`, and `ψ : B_𝔭 → R` a homomorphism extending `φ`. Then `ψ` is
injective, and its image is the set of fractions `a / s` with `a, s ∈ φ(B)` and `v_R(s) = 1`. -/
private theorem injective_and_range_of_isLocalization_atPrime {K : Type*} [Field K]
    (R : ValuationSubring K) {B T : Type*} [CommRing B] [CommRing T] [Algebra B T]
    (φK : B →+* K) (hinj : Function.Injective φK) (p : Ideal B) [p.IsPrime]
    (hp : ∀ b, b ∉ p ↔ R.valuation (φK b) = 1) [IsLocalization.AtPrime T p] (ψ : T →+* R)
    (hψ : ∀ b, (ψ (algebraMap B T b) : K) = φK b) :
    Function.Injective ψ ∧ Set.range (fun t => (ψ t : K)) =
      {y | ∃ a ∈ Set.range φK, ∃ s ∈ Set.range φK, R.valuation s = 1 ∧ y * s = a} := by
  have key : ∀ (b : B) (s : p.primeCompl), (ψ (mk' T b s) : K) * φK s = φK b := by
    intro b s
    rw [← hψ, ← hψ, ← Subring.coe_mul, ← map_mul, mk'_spec]
  have hs0 : ∀ s : p.primeCompl, φK s ≠ 0 := fun s h => by
    have := (hp s).mp s.2
    rw [h, map_zero] at this
    exact zero_ne_one this
  refine ⟨(injective_iff_map_eq_zero ψ).mpr fun t ht => ?_, Set.ext fun y => ⟨?_, ?_⟩⟩
  · obtain ⟨⟨b, s⟩, rfl⟩ := mk'_surjective p.primeCompl t
    have := key b s
    rw [ht, ZeroMemClass.coe_zero, zero_mul, eq_comm, map_eq_zero_iff _ hinj] at this
    simp [this]
  · rintro ⟨t, rfl⟩
    obtain ⟨⟨b, s⟩, rfl⟩ := mk'_surjective p.primeCompl t
    exact ⟨_, ⟨b, rfl⟩, _, ⟨s, rfl⟩, (hp s).mp s.2, key b s⟩
  · rintro ⟨_, ⟨b, rfl⟩, _, ⟨s, rfl⟩, hv, hy⟩
    let s' : p.primeCompl := ⟨s, (hp s).mpr hv⟩
    exact ⟨mk' T b s', mul_right_cancel₀ (hs0 s') ((key b s').trans hy.symm)⟩

open IsLocalization in
/-- Let `𝒪` be a ring with fraction field `K`, `e : Γ ≃ 𝒪` a ring isomorphism, `I ⊆ Γ` the
transport of the ideal generated by `z_1, …, z_r`, and `a = e⁻¹(z_{i₀}) ≠ 0`. Then
`Γ_a → K` is injective and carries the affine blow-up algebra `Γ[I/a]` onto
`𝒪[z_1/z_{i₀}, …, z_r/z_{i₀}] ⊆ K`. -/
private theorem exists_injective_image_affineBlowupAlgebra {𝒪 K Γ : Type*} [CommRing 𝒪]
    [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [CommRing Γ] (e : Γ ≃+* 𝒪)
    {r : ℕ} (z : Fin r → 𝒪) (i₀ : Fin r) (hz0 : z i₀ ≠ 0) (I' : Ideal Γ)
    (hI' : I' = Ideal.map e.symm (Ideal.span (Set.range z))) (a' : Γ) (ha' : e a' = z i₀) :
    ∃ Λ : Localization.Away a' →+* K, Function.Injective Λ ∧
      (∀ c : Γ, Λ (algebraMap Γ _ c) = algebraMap 𝒪 K (e c)) ∧
      Λ '' (affineBlowupAlgebra I' a' (Localization.Away a') : Set (Localization.Away a')) =
        (Algebra.adjoin 𝒪 (Set.range fun j => algebraMap 𝒪 K (z j) / algebraMap 𝒪 K (z i₀)) :
          Set K) := by
  set g : Γ →+* K := (algebraMap 𝒪 K).comp e.toRingHom
  have hg : Function.Injective g := (IsFractionRing.injective 𝒪 K).comp e.injective
  have hga : g a' = algebraMap 𝒪 K (z i₀) := by simp [g, ha']
  have hga0 : g a' ≠ 0 := by
    rw [hga]
    exact (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).mpr hz0
  let Λ : Localization.Away a' →+* K := IsLocalization.Away.lift a' (g := g) (Ne.isUnit hga0)
  have hΛ : ∀ c, Λ (algebraMap Γ _ c) = g c := fun c => IsLocalization.lift_eq _ _
  have key : ∀ (y : Γ) (s : Submonoid.powers a'), Λ (mk' _ y s) * g s = g y := by
    intro y s
    rw [← hΛ, ← hΛ, ← map_mul, mk'_spec]
  set A := Algebra.adjoin 𝒪 (Set.range fun j => algebraMap 𝒪 K (z j) / algebraMap 𝒪 K (z i₀))
  have hmemI : ∀ y, y ∈ I' ↔ e y ∈ Ideal.span (Set.range z) := by
    intro y
    rw [hI', Ideal.map_symm]
    rfl
  have hgen : ∀ y, Λ (mk' _ y (⟨a', Submonoid.mem_powers a'⟩ : Submonoid.powers a')) =
      algebraMap 𝒪 K (e y) / algebraMap 𝒪 K (z i₀) := by
    intro y
    rw [eq_div_iff (hga ▸ hga0), ← hga]
    exact key y ⟨a', _⟩
  refine ⟨Λ, (injective_iff_map_eq_zero Λ).mpr fun w hw => ?_, hΛ, ?_⟩
  · obtain ⟨⟨y, s⟩, rfl⟩ := mk'_surjective (Submonoid.powers a') w
    have := key y s
    rw [hw, zero_mul, eq_comm, map_eq_zero_iff _ hg] at this
    simp [this]
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    let P : Subalgebra Γ (Localization.Away a') :=
      { (A.toSubring.comap Λ) with
        algebraMap_mem' := fun c => by
          change Λ _ ∈ A
          rw [hΛ]
          exact A.algebraMap_mem _ }
    have : affineBlowupAlgebra I' a' (Localization.Away a') ≤ P := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨y, hy, rfl⟩
      change Λ _ ∈ A
      rw [hgen y]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪).mp ((hmemI y).mp hy)
      rw [← hc, map_sum, Finset.sum_div]
      refine Subalgebra.sum_mem _ fun j _ => ?_
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact A.mul_mem (A.algebraMap_mem _) (Algebra.subset_adjoin ⟨j, rfl⟩)
    exact this hw
  · let Q : Subalgebra 𝒪 K :=
      { ((affineBlowupAlgebra I' a' (Localization.Away a')).toSubring.map Λ) with
        algebraMap_mem' := fun s => ⟨algebraMap Γ _ (e.symm s),
          Subalgebra.algebraMap_mem _ _, by simp [hΛ, g]⟩ }
    have : A ≤ Q := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      have hj : e.symm (z j) ∈ I' := (hmemI _).mpr (by
        rw [RingEquiv.apply_symm_apply]
        exact Ideal.subset_span (Set.mem_range_self j))
      have hm : mk' (Localization.Away a') (e.symm (z j))
          (⟨a', Submonoid.mem_powers a'⟩ : Submonoid.powers a') ∈
            affineBlowupAlgebra I' a' (Localization.Away a') :=
        Algebra.subset_adjoin ⟨_, hj, rfl⟩
      refine ⟨_, hm, ?_⟩
      simp only [hgen _, RingEquiv.apply_symm_apply]
    exact fun y hy => this hy

/-- For a morphism `f : Spec R ⟶ Y` from a local scheme and an open immersion `ι : Y ⟶ Z`, the
homomorphism `𝒪_{Z, ι(f(closed point))} ⟶ R` of `f ≫ ι` is that of `f` up to a bijection; in
particular it is injective when that of `f` is, and both have the same image. -/
private theorem injective_and_range_stalkClosedPointTo_of_eq_comp {R : CommRingCat.{u}}
    [IsLocalRing R] {Y Z : Scheme.{u}} {g : Spec R ⟶ Z} (f : Spec R ⟶ Y) (ι : Y ⟶ Z)
    [IsOpenImmersion ι] (h : g = f ≫ ι) :
    (Function.Injective (Scheme.stalkClosedPointTo f).hom →
      Function.Injective (Scheme.stalkClosedPointTo g).hom) ∧
    ∀ {W : Type*} (F : R → W), Set.range (fun t => F ((Scheme.stalkClosedPointTo g).hom t)) =
      Set.range (fun t => F ((Scheme.stalkClosedPointTo f).hom t)) := by
  subst h
  rw [Scheme.stalkClosedPointTo_comp]
  have hb : Function.Bijective (ι.stalkMap (f (IsLocalRing.closedPoint R))).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨fun hf => ?_, fun F => ?_⟩
  · exact hf.comp hb.1
  · exact hb.2.range_comp (fun t => F ((Scheme.stalkClosedPointTo f).hom t))

private theorem ne_zero_of_valuation_le_of_span_eq {X : Scheme.{u}} [IsIntegral X] (x : X)
    {r : ℕ} (z : Fin r → X.presheaf.stalk x)
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≠ ⊥)
    (R : ValuationSubring X.functionField) (i₀ : Fin r)
    (hval : ∀ j, R.valuation (algebraMap _ X.functionField (z j)) ≤
        R.valuation (algebraMap _ X.functionField (z i₀))) :
    z i₀ ≠ 0 := by
  intro h0
  apply hm
  rw [← hz, Ideal.span_eq_bot]
  rintro _ ⟨j, rfl⟩
  have := hval j
  rwa [h0, map_zero, map_zero, le_zero_iff, map_eq_zero,
    map_eq_zero_iff _ (IsFractionRing.injective _ _)] at this

private theorem mem_of_mem_adjoin_div_of_valuation_le {X : Scheme.{u}} [IsIntegral X] (x : X)
    {r : ℕ} (z : Fin r → X.presheaf.stalk x) (R : ValuationSubring X.functionField)
    (hR : Stacks.AffineBlowup.Dominates (X.presheaf.stalk x) R) (i₀ : Fin r)
    (hval : ∀ j, R.valuation (algebraMap _ X.functionField (z j)) ≤
        R.valuation (algebraMap _ X.functionField (z i₀))) :
    ∀ y ∈ Algebra.adjoin (X.presheaf.stalk x)
      (Set.range fun j => algebraMap _ X.functionField (z j) /
        algebraMap _ X.functionField (z i₀)), y ∈ R := by
  let R' : Subalgebra (X.presheaf.stalk x) X.functionField :=
    { R.toSubring with algebraMap_mem' := fun s => hR.1 ⟨s, rfl⟩ }
  have : Algebra.adjoin (X.presheaf.stalk x)
      (Set.range fun j => algebraMap _ X.functionField (z j) /
        algebraMap _ X.functionField (z i₀)) ≤ R' := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    refine R.mem_of_valuation_le_one _ ?_
    rw [map_div₀]
    exact div_le_one_of_le₀ (hval j) zero_le
  exact fun y hy => this hy

private theorem eq_of_comp_blowUpToBase_eq {X : Scheme.{u}} [IsIntegral X] (x : X) {r : ℕ}
    (z : Fin r → X.presheaf.stalk x)
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (R : ValuationSubring X.functionField)
    (hR : Stacks.AffineBlowup.Dominates (X.presheaf.stalk x) R) (i₀ : Fin r) (hz0 : z i₀ ≠ 0)
    (J : (Spec (.of (X.presheaf.stalk x))).IdealSheafData)
    (hJdef : J = Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map (Scheme.ΓSpecIso _).inv.hom))
    [IsSeparated (blowUpToBase J)] (g g₀ : Spec (.of R) ⟶ blowUp J)
    (hg : g ≫ blowUpToBase J = Spec.map (CommRingCat.ofHom
        ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict R.toSubring
          (fun s => hR.1 ⟨s, rfl⟩))))
    (hg₀ : g₀ ≫ blowUpToBase J = g ≫ blowUpToBase J) : g = g₀ := by
  let c : Spec (.of R) ⟶ Spec (.of (X.presheaf.stalk x)) := Spec.map (CommRingCat.ofHom
    ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict R.toSubring
      (fun s => hR.1 ⟨s, rfl⟩)))
  have hgc : g ≫ blowUpToBase J = c := hg
  have hg₀c : g₀ ≫ blowUpToBase J = c := hg₀.trans hg
  have hmono :
      Mono (blowUpToBase J ∣_ Stacks.AlgebraicGeometry.BlowUpUniversal.supportCompl J) :=
    have := isIso_blowUp_restrict_compl_support J
    inferInstance
  have hne : ((c ⁻¹ᵁ Stacks.AlgebraicGeometry.BlowUpUniversal.supportCompl J :
      (Spec (.of R)).Opens) : Set (Spec (.of R))).Nonempty := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    change c _ ∉ (J.support : Set _)
    rw [hJdef, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
    intro hmem
    have h1 := hmem (show z i₀ ∈ (Scheme.ΓSpecIso _).inv.hom ⁻¹' _ from
      Ideal.mem_map_of_mem _ (hz ▸ Ideal.subset_span (Set.mem_range_self i₀)))
    apply hz0
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_zero]
    exact congrArg Subtype.val (Ideal.mem_bot.mp h1)
  have : IsDominant (c ⁻¹ᵁ Stacks.AlgebraicGeometry.BlowUpUniversal.supportCompl J).ι :=
    Opens.isDominant_ι ((c ⁻¹ᵁ _).isOpen.dense hne)
  exact ext_of_isDominant_of_isSeparated (blowUpToBase J) (hgc.trans hg₀c.symm) _
    (Stacks.AlgebraicGeometry.BlowUpUniversal.ι_comp_eq_of_mono J hmono g g₀ hgc hg₀c)

private theorem injective_and_range_stalkMap_of_eq_comp_Spec_map {K : Type u} [Field K]
    (R : ValuationSubring K) {B : Type u} [CommRing B] (φK : B →+* K)
    (hinj : Function.Injective φK) (φ : B →+* R) (hφ : ∀ b, (φ b : K) = φK b)
    {Z : Scheme.{u}} (ι : Spec (.of B) ⟶ Z) [IsOpenImmersion ι] (g : Spec (.of R) ⟶ Z)
    (hg : g = Spec.map (CommRingCat.ofHom φ) ≫ ι) :
    Function.Injective
        (g.stalkMap (IsLocalRing.closedPoint R) ≫ (stalkClosedPointIso (.of R)).hom).hom ∧
      Set.range (fun t => ((g.stalkMap (IsLocalRing.closedPoint R) ≫
          (stalkClosedPointIso (.of R)).hom).hom t : K)) =
        {y | ∃ a ∈ Set.range φK, ∃ s ∈ Set.range φK, R.valuation s = 1 ∧ y * s = a} := by
  let pt : PrimeSpectrum B := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint R)
  let k : Algebra B ((Spec (.of B)).presheaf.stalk pt) := StructureSheaf.stalkAlgebra B pt
  have : IsLocalization.AtPrime ((Spec (.of B)).presheaf.stalk pt) pt.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B pt
  have hp : ∀ b, b ∉ pt.asIdeal ↔ R.valuation (φK b) = 1 := by
    intro b
    change ¬ (φ b ∈ IsLocalRing.maximalIdeal R) ↔ _
    rw [R.valuation_lt_one_iff, ← hφ]
    exact (R.valuation_le_one (φ b)).not_lt_iff_eq
  have hψ₀ : ∀ b, ((Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ))).hom
      (algebraMap B _ b) : K) = φK b := by
    intro b
    have := congrArg (fun f => (f.hom ((Scheme.ΓSpecIso (.of B)).inv b) : K))
      (Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at this
    exact this.trans (hφ b)
  obtain ⟨h1, h2⟩ := injective_and_range_of_isLocalization_atPrime R φK hinj pt.asIdeal hp _ hψ₀
  obtain ⟨hic, hrc⟩ := injective_and_range_stalkClosedPointTo_of_eq_comp _ ι hg
  exact ⟨hic h1, (hrc _).trans h2⟩

/-- **The local ring selected by a valuation on the blow-up of a local ring.** Let `𝒪 = 𝒪_{X,x}`
with nonzero maximal ideal generated by `z_1, …, z_r`, `R` a valuation ring of `k(X)` dominating
`𝒪` for which `z_{i₀}` has the least valuation, and `g : Spec R ⟶ Bl_𝔪 Spec 𝒪` a morphism over
`Spec 𝒪` (with `Bl_𝔪 Spec 𝒪 ⟶ Spec 𝒪` separated). Then the local homomorphism `𝒪_{Bl, g(closed point)} ⟶ R` is injective, with image
the localization of `A = 𝒪[z_j / z_{i₀}]` at `A ∩ 𝔪_R`. -/
private theorem stalkMap_blowUp_maximalIdeal_valuation_chart {X : Scheme.{u}} [IsIntegral X]
    (x : X) {r : ℕ} (z : Fin r → X.presheaf.stalk x)
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≠ ⊥)
    (R : ValuationSubring X.functionField)
    (hR : Stacks.AffineBlowup.Dominates (X.presheaf.stalk x) R) (i₀ : Fin r)
    (hval : ∀ j, R.valuation (algebraMap _ X.functionField (z j)) ≤
        R.valuation (algebraMap _ X.functionField (z i₀)))
    (J : (Spec (.of (X.presheaf.stalk x))).IdealSheafData)
    (hJdef : J = Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map (Scheme.ΓSpecIso _).inv.hom))
    [IsSeparated (blowUpToBase J)] (g : Spec (.of R) ⟶ blowUp J)
    (hg : g ≫ blowUpToBase J = Spec.map (CommRingCat.ofHom
        ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict R.toSubring
          (fun s => hR.1 ⟨s, rfl⟩)))) :
    let A := Algebra.adjoin (X.presheaf.stalk x)
      (Set.range fun j => algebraMap _ X.functionField (z j) /
        algebraMap _ X.functionField (z i₀))
    let ψ := (g.stalkMap (IsLocalRing.closedPoint R) ≫
      (stalkClosedPointIso (.of R)).hom).hom
    Function.Injective ψ ∧
      Set.range (fun t => (ψ t : X.functionField)) =
        {y | ∃ a ∈ A, ∃ s ∈ A, R.valuation s = 1 ∧ y * s = a} := by
  intro A ψ
  classical
  let U : (Spec (.of (X.presheaf.stalk x))).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let e : Γ(Spec (.of (X.presheaf.stalk x)), ⊤) ≃+* X.presheaf.stalk x :=
    (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
  have hJU : J.ideal U = Ideal.map e.symm (Ideal.span (Set.range z)) := by
    subst hJdef
    rw [hz, ofIdealTop_ideal_top]
    rfl
  have hz0 := ne_zero_of_valuation_le_of_span_eq x z hz hm R i₀ hval
  have ha : e.symm (z i₀) ∈ J.ideal U :=
    hJU ▸ Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i₀, rfl⟩)
  let a : J.ideal U := ⟨e.symm (z i₀), ha⟩
  obtain ⟨Λ, hΛinj, hΛ, hΛA⟩ := exists_injective_image_affineBlowupAlgebra
    (K := X.functionField) e z i₀ hz0 (J.ideal U) hJU (e.symm (z i₀)) (e.apply_symm_apply _)
  let B := blowUpAffineChartRing J U a
  let φK : B →+* X.functionField := Λ.comp (Subalgebra.val _).toRingHom
  have hφKinj : Function.Injective φK := hΛinj.comp Subtype.val_injective
  have hφA : Set.range φK = A := by
    rw [← hΛA]
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hAR := mem_of_mem_adjoin_div_of_valuation_le x z R hR i₀ hval
  let φ : B →+* R := φK.codRestrict R.toSubring fun b =>
    hAR _ (show φK b ∈ (A : Set _) from hφA ▸ Set.mem_range_self b)
  let g₀ : Spec (.of R) ⟶ blowUp J :=
    Spec.map (CommRingCat.ofHom φ) ≫ blowUpAffineChart J U a
  have hg₀ : g₀ ≫ blowUpToBase J = g ≫ blowUpToBase J := by
    rw [hg]
    simp only [g₀, Category.assoc, blowUpAffineChart_comp_blowUpToBase]
    change Spec.map _ ≫ Spec.map _ ≫ (isAffineOpen_top _).fromSpec = _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext s
    change Λ (algebraMap _ _ ((Scheme.ΓSpecIso _).inv s)) = _
    rw [hΛ]
    exact congrArg (algebraMap _ X.functionField) (e.apply_symm_apply s)
  obtain ⟨h1, h2⟩ := injective_and_range_stalkMap_of_eq_comp_Spec_map R φK hφKinj φ
    (fun _ => rfl) (blowUpAffineChart J U a) g
    (eq_of_comp_blowUpToBase_eq x z hz R hR i₀ hz0 J hJdef g g₀ hg hg₀)
  refine ⟨h1, h2.trans ?_⟩
  rw [hφA]
  rfl

/-- **The blow-up at a point closure and the chart selected by a valuation.** Let `k₀` be a
field and `X` an integral scheme, separated and of finite type over `k₀` via `sX`; let `x` be a
point other than the generic point, `I` the reduced ideal sheaf of `closure {x}`, and
`z : Fin r → 𝒪_{X,x}` generators of the maximal ideal. Then:

* `blowUp I` is integral and `blowUpToBase I` is proper and birational;
* the base change of `blowUpToBase I` along `X.fromSpecStalk x` is the blow-up of
  `Spec 𝒪_{X,x}` in the ideal sheaf `J` of the maximal ideal, and the charts
  `blowUpChartOpen J ⊤ (z j)` cover it;
* if `R` is a valuation subring of `X.functionField` dominating `𝒪_{X,x}` with
  `R.valuation (z j) ≤ R.valuation (z i₀)` for all `j`, then `fromSpecOfStalkLE x R _` lifts
  along `blowUpToBase I`, and for every lift `g` the map `𝒪_{X',g(closed point)} ⟶ R` induced
  by `g` is injective with image, in the function field, the localization of
  `A = 𝒪_{X,x}[z_j / z_{i₀}]` at the prime `A ∩ 𝔪_R`, i.e. `{a / s | a, s ∈ A, v_R(s) = 1}`. -/
@[mmp "lem_mmp_foundation_valuation_blowup_local_chart"]
public theorem blowUp_vanishingIdeal_closure_valuation_chart {k₀ : Type u} [Field k₀]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k₀)) [IsIntegral X] [IsSeparated sX]
    [LocallyOfFiniteType sX] [QuasiCompact sX] (x : X) (hx : x ≠ genericPoint X) {r : ℕ}
    (z : Fin r → X.presheaf.stalk x)
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})
    let J : (Spec (.of (X.presheaf.stalk x))).IdealSheafData :=
      Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map (Scheme.ΓSpecIso _).inv.hom)
    (IsIntegral (blowUp I) ∧ IsProper (blowUpToBase I) ∧ IsBirational (blowUpToBase I)) ∧
    (∃ h : blowUp J ⟶ blowUp I,
      IsPullback (blowUpToBase J) h (X.fromSpecStalk x) (blowUpToBase I)) ∧
    (∀ a : Fin r → J.ideal ⟨⊤, isAffineOpen_top _⟩,
      (∀ j, (a j : Γ(Spec (.of (X.presheaf.stalk x)), ⊤)) = (Scheme.ΓSpecIso _).inv (z j)) →
      ⨆ j, (blowUpChartOpen J ⟨⊤, isAffineOpen_top _⟩ (a j)).1 = ⊤) ∧
    ∀ (R : ValuationSubring X.functionField)
      (hR : Stacks.AffineBlowup.Dominates (X.presheaf.stalk x) R) (i₀ : Fin r),
      (∀ j, R.valuation (algebraMap _ X.functionField (z j)) ≤
        R.valuation (algebraMap _ X.functionField (z i₀))) →
      (∃ g : Spec (.of R) ⟶ blowUp I,
        g ≫ blowUpToBase I = fromSpecOfStalkLE x R.toSubring (fun s => hR.1 ⟨s, rfl⟩)) ∧
      ∀ g : Spec (.of R) ⟶ blowUp I,
        g ≫ blowUpToBase I = fromSpecOfStalkLE x R.toSubring (fun s => hR.1 ⟨s, rfl⟩) →
        let A := Algebra.adjoin (X.presheaf.stalk x)
          (Set.range fun j => algebraMap _ X.functionField (z j) /
            algebraMap _ X.functionField (z i₀))
        let ψ := (g.stalkMap (IsLocalRing.closedPoint R) ≫
          (stalkClosedPointIso (.of R)).hom).hom
        Function.Injective ψ ∧
          Set.range (fun t => (ψ t : X.functionField)) =
            {y | ∃ a ∈ A, ∃ s ∈ A, R.valuation s = 1 ∧ y * s = a} := by
  intro I J
  have hI : I ≠ ⊥ := vanishingIdeal_closure_ne_bot x hx
  have : AlgebraicGeometry.IsVariety k₀ sX := { }
  obtain ⟨-, hproj, hbir⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sX I hI
  have hprop : IsProper (blowUpToBase I) := hproj.isProper
  have hJ : I.comap (X.fromSpecStalk x) = J := vanishingIdeal_closure_comap_fromSpecStalk x
  have hflat : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  obtain ⟨h, hpb⟩ : ∃ h : blowUp J ⟶ blowUp I,
      IsPullback (blowUpToBase J) h (X.fromSpecStalk x) (blowUpToBase I) := by
    rw [← hJ]
    exact exists_isPullback_blowUpToBase_comap (X.fromSpecStalk x) I
  refine ⟨⟨isIntegral_blowUp I hI, hprop, hbir⟩, ⟨h, hpb⟩, ?_, ?_⟩
  · intro a ha
    refine (iSup_blowUpChartOpen_eq_preimage J _ a ?_).trans (Scheme.Hom.preimage_top _)
    rw [show (fun j => (a j : Γ(Spec (.of (X.presheaf.stalk x)), ⊤))) = _ from funext ha]
    change _ = (Scheme.IdealSheafData.ofIdealTop _).ideal ⟨⊤, isAffineOpen_top _⟩
    rw [ofIdealTop_ideal_top, ← hz, Ideal.map_span, ← Set.range_comp]
    rfl
  · intro R hR i₀ hval
    refine ⟨exists_comp_blowUpToBase_eq_fromSpecOfStalkLE I hI x R _, fun g hg => ?_⟩
    let c : Spec (.of R) ⟶ Spec (.of (X.presheaf.stalk x)) := Spec.map (CommRingCat.ofHom
      ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict R.toSubring
        (fun s => hR.1 ⟨s, rfl⟩)))
    obtain ⟨g', h₁, rfl⟩ : ∃ g' : Spec (.of R) ⟶ blowUp J, g' ≫ blowUpToBase J = c ∧ g' ≫ h = g :=
      ⟨hpb.lift c g hg.symm, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
    have : Flat h := MorphismProperty.of_isPullback (P := @Flat) hpb hflat
    have : IsPreimmersion h :=
      MorphismProperty.of_isPullback (P := @IsPreimmersion) hpb inferInstance
    have : IsProper (blowUpToBase J) :=
      MorphismProperty.of_isPullback (P := @IsProper) hpb.flip hprop
    obtain ⟨hinj, hrange⟩ := stalkMap_blowUp_maximalIdeal_valuation_chart x z hz
      (maximalIdeal_stalk_ne_bot x hx) R hR i₀ hval J rfl g' h₁
    have hbij := bijective_stalkMap_of_flat_of_isPreimmersion h (g' (IsLocalRing.closedPoint R))
    intro A ψ
    have hψ : ⇑ψ = (g'.stalkMap (IsLocalRing.closedPoint R) ≫
        (stalkClosedPointIso (.of R)).hom).hom ∘
          (h.stalkMap (g' (IsLocalRing.closedPoint R))).hom := by
      funext t
      simp only [ψ]
      erw [Scheme.Hom.stalkMap_comp]
      rfl
    refine ⟨hψ ▸ hinj.comp hbij.1, ?_⟩
    rw [← hrange, hψ]
    exact hbij.2.range_comp (fun t => ((g'.stalkMap (IsLocalRing.closedPoint R) ≫
        (stalkClosedPointIso (.of R)).hom).hom t : X.functionField))

end MMP.Mori

/-! ### Embedding dimension -/

namespace MMP

open IsLocalRing

/-- The Krull dimension of a Noetherian local ring is at most the dimension of its cotangent
space `𝔪 / 𝔪²` over the residue field. -/
@[mmp "lem_mmp_resolution_dimension_le_embedding_dimension"]
public theorem ringKrullDim_le_finrank_cotangentSpace (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ringKrullDim R ≤ (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

end MMP
