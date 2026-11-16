module
public import Mathlib
public import MMP.Attr
import MMP.Analysis.Complex.StratifiedFlows

/-!
# Product germs along a proper relative SNC divisor

Let `g : Z → B` be a holomorphic map from a Hausdorff, second countable complex manifold `Z` of
dimension `n` to a complex curve `B`, and let `E = ⋃ i, D i` be a closed simple normal crossing
divisor on `Z` with smooth components `D i`, proper over `B`. Suppose `g` is a submersion on a
neighbourhood of `E`, and that at every point `x ∈ E` the restriction of `g` to the deepest
stratum `⋂_{x ∈ D i} D i` through `x` is a submersion (so that its restriction to every
intersection stratum of `E` is a submersion). Then, over a small coordinate disk `Δ` about any
`b ∈ B`, a neighbourhood of `E_Δ` in `Z_Δ` is homeomorphic over `Δ` to `U_b × Δ`, where `U_b` is a
neighbourhood of `E_b` in the fibre `Z_b`; the homeomorphism is the identity over `b` and
preserves every component `D i`, hence every intersection of components and `E` itself.

## Main results

* `MMP.Analytic.exists_homeomorph_prod_of_relativeSNC`: the product germ.

## Implementation notes

* A complex manifold of dimension `n` is expressed by Mathlib's classes `ChartedSpace
  (EuclideanSpace ℂ (Fin n)) Z` and `IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z`; a complex
  curve by `ChartedSpace ℂ B` and `IsManifold 𝓘(ℂ) ∞ B`. Holomorphy of `g` is
  `MDifferentiable`, and its differential is `mfderiv`.
* The SNC divisor is a family `D : ι → Set Z` of smooth hypersurfaces with simultaneous
  coordinate charts: every point of `Z` is in the source of a chart `φ` of the maximal holomorphic
  atlas, a finite set `s` of indices and an injection `c : s ↪ Fin n` such that `D i` misses the
  chart for `i ∉ s`, and `φ(D i ∩ W) = φ(W) ∩ {y_{c i} = 0}` for `i ∈ s`. The family need not be
  finite; the charts make it locally finite.
* The tangent space at `x` of the stratum `S = ⋂_{x ∈ D i} D i` is the tangent cone of `S` at `x`,
  read in the preferred extended chart at `x` (the coordinates in which `mfderiv` is computed).
  As `S` is a complex submanifold near `x`, this cone is a `ℂ`-linear subspace, and since `B` is a
  curve, `g|_S` is a submersion at `x` exactly when `dg_x` is nonzero on it.
* The disk `Δ` is the preimage, under a holomorphic chart `ψ` of `B`, of a round disk about
  `ψ b` contained in the target of `ψ`; it can be chosen inside any given neighbourhood of `b`.
  Fibres are subsets of `Z`: `U_b ⊆ g⁻¹{b}` is open in the fibre, and `U ⊆ g⁻¹ Δ` is open in `Z`.
* The proof is the stratified Ehresmann argument. The real coordinate fields `∂_s, ∂_u` of the
  disk lift to fields near `E` tangent to every component, whose flows are
  `MMP.Analytic.StratifiedFlows.exists_horizontal_flows`; the trivialization is the composite
  `Φ (z, s + i u) = φ^{V_u}_u (φ^{V_s}_s z)`, with inverse the reversed flows.
-/

open Set Topology Filter
open scoped Manifold ContDiff

namespace MMP.Analytic

/-- The core of the product-germ statement: in the preferred chart `ψ` of `B` at `b`, for every
sufficiently small radius `r`, a neighbourhood of `E` over the disk `Δ_r` is trivialized over
`Δ_r`, as the identity at `b` and preserving every `D i`. -/
private lemma eventually_exists_homeomorph_prod_ball
    {n : ℕ} {Z B : Type*} [TopologicalSpace Z] [T2Space Z] [SecondCountableTopology Z]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) Z]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z]
    [TopologicalSpace B] [T2Space B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ∞ B]
    {g : Z → B} (hg : MDifferentiable 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g)
    {ι : Type*} {D : ι → Set Z}
    (hD : ∀ x : Z, ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z,
      x ∈ φ.source ∧ ∃ (s : Finset ι) (c : s ↪ Fin n),
        (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
        ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0})
    (hproper : IsProperMap (fun x : (⋃ i, D i : Set Z) => g x))
    (hsubmersion : ∃ W : Set Z, IsOpen W ∧ (⋃ i, D i) ⊆ W ∧
      ∀ x ∈ W, Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x))
    (hstrata : ∀ x ∈ ⋃ i, D i, ∃ v ∈ tangentConeAt ℂ
        ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).target ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).symm ⁻¹' ⋂ (i) (_ : x ∈ D i), D i)
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x),
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x v ≠ 0)
    (b : B) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      let Δ : Set B := (chartAt ℂ b).source ∩ (chartAt ℂ b) ⁻¹' Metric.ball (chartAt ℂ b b) r
      ∃ (Ub U : Set Z) (hb : b ∈ Δ),
        Ub ⊆ g ⁻¹' {b} ∧ (∃ O : Set Z, IsOpen O ∧ Ub = O ∩ g ⁻¹' {b}) ∧
        (⋃ i, D i) ∩ g ⁻¹' {b} ⊆ Ub ∧
        IsOpen U ∧ U ⊆ g ⁻¹' Δ ∧ (⋃ i, D i) ∩ g ⁻¹' Δ ⊆ U ∧
        ∃ Φ : Ub × Δ ≃ₜ U,
          (∀ p : Ub × Δ, g (Φ p) = p.2) ∧
          (∀ z : Ub, (Φ (z, ⟨b, hb⟩) : Z) = z) ∧
          ∀ (i : ι) (p : Ub × Δ), (Φ p : Z) ∈ D i ↔ (p.1 : Z) ∈ D i := by
  have hgc : Continuous g := hg.continuous
  obtain ⟨ε, hε, Ω, F, hΩo, hΩs, hΩ0, hEΩ, hF⟩ :=
    MMP.Analytic.StratifiedFlows.exists_horizontal_flows hg hD hproper hsubmersion hstrata b
  obtain ⟨h1_0, h1_c, h1⟩ := hF 1 (by simp)
  obtain ⟨hI_0, hI_c, hI⟩ := hF Complex.I (by simp)
  have hanti : Antitone Ω := antitone_nat_of_succ_le hΩs
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  intro Δ
  set ψ := chartAt ℂ b
  set c := ψ b with hc
  have hbs : b ∈ ψ.source := mem_chart_source ℂ b
  have hΔo : IsOpen Δ := ψ.isOpen_inter_preimage Metric.isOpen_ball
  have hb : b ∈ Δ := ⟨hbs, by simp [hr.1]⟩
  have hΔε : ∀ y ∈ Δ, y ∈ ψ.source ∩ ψ ⁻¹' Metric.ball c ε :=
    fun y hy => ⟨hy.1, Metric.ball_subset_ball hr.2.le hy.2⟩
  have hw : ∀ y ∈ Δ, (ψ y - c).re ∈ Ioo (-ε) ε ∧ (ψ y - c).im ∈ Ioo (-ε) ε := by
    intro y hy
    have h : ‖ψ y - c‖ < ε := (mem_ball_iff_norm.mp hy.2).trans hr.2
    exact ⟨abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt h),
      abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt h)⟩
  have hneg : ∀ t ∈ Ioo (-ε) ε, -t ∈ Ioo (-ε) ε := fun t ht =>
    ⟨neg_lt_neg ht.2, neg_lt.mpr ht.1⟩
  have hEΩ' : ∀ k ≤ 4, (⋃ i, D i) ∩ g ⁻¹' Δ ⊆ Ω k :=
    fun k hk x hx => hEΩ k hk ⟨hx.1, hΔε _ hx.2⟩
  let Φf : Z → B → Z := fun z y => F Complex.I (ψ y - c).im (F 1 (ψ y - c).re z)
  let Gf : Z → Z := fun x =>
    F 1 (-(ψ (g x) - c).re) (F Complex.I (-(ψ (g x) - c).im) x)
  have hfwd : ∀ z ∈ Ω 4, g z = b → ∀ y ∈ Δ,
      Φf z y ∈ Ω 2 ∧ g (Φf z y) = y ∧ Gf (Φf z y) = z ∧ ∀ i, (Φf z y ∈ D i ↔ z ∈ D i) := by
    intro z hz hgz y hy
    obtain ⟨ha, ht⟩ := hw y hy
    obtain ⟨hu, hgu, hu1, hDu⟩ := h1 3 z hz _ ha
    obtain ⟨hv, hgv, hv1, hDv⟩ := hI 2 _ hu _ ht
    have hgΦ : g (Φf z y) = y := by
      refine ψ.injOn (hΩ0 (hanti (by norm_num) hv)) hy.1 ?_
      rw [hgv, hgu, hgz, ← hc]
      linear_combination Complex.re_add_im (ψ y - c)
    refine ⟨hv, hgΦ, ?_, fun i => (hDv i).trans (hDu i)⟩
    change F 1 (-(ψ (g (Φf z y)) - c).re) (F Complex.I (-(ψ (g (Φf z y)) - c).im) _) = z
    rw [hgΦ]
    change F 1 _ (F Complex.I _ (F Complex.I _ _)) = z
    rw [hv1, hu1]
  have hbwd : ∀ x ∈ Ω 2, g x ∈ Δ →
      Gf x ∈ Ω 0 ∧ g (Gf x) = b ∧ Φf (Gf x) (g x) = x ∧ ∀ i, (Gf x ∈ D i ↔ x ∈ D i) := by
    intro x hx hgx
    obtain ⟨ha, ht⟩ := hw _ hgx
    obtain ⟨hv, hgv, hv1, hDv⟩ := hI 1 x hx _ (hneg _ ht)
    obtain ⟨hu, hgu, hu1, hDu⟩ := h1 0 _ hv _ (hneg _ ha)
    have hgG : g (Gf x) = b := by
      refine ψ.injOn (hΩ0 hu) hbs ?_
      rw [hgu, hgv, ← hc]
      push_cast
      linear_combination -Complex.re_add_im (ψ (g x) - c)
    refine ⟨hu, hgG, ?_, fun i => (hDu i).trans (hDv i)⟩
    change F Complex.I (ψ (g x) - c).im (F 1 (ψ (g x) - c).re (F 1 _ _)) = x
    rw [neg_neg] at hu1 hv1
    rw [hu1, hv1]
  have hpc : ContinuousOn (fun x => ψ (g x)) (g ⁻¹' Δ) :=
    ψ.continuousOn.comp hgc.continuousOn (fun x hx => hx.1)
  have hGc : ContinuousOn Gf (Ω 2 ∩ g ⁻¹' Δ) := by
    have hwc : ContinuousOn (fun x => ψ (g x) - c) (Ω 2 ∩ g ⁻¹' Δ) :=
      (hpc.mono inter_subset_right).sub continuousOn_const
    have hin : ContinuousOn (fun x => F Complex.I (-(ψ (g x) - c).im) x) (Ω 2 ∩ g ⁻¹' Δ) :=
      hI_c.comp (f := fun x => (-(ψ (g x) - c).im, x))
        ((Complex.continuous_im.comp_continuousOn hwc).neg.prodMk continuousOn_id)
        (fun x hx => ⟨hneg _ (hw _ hx.2).2, hanti (by norm_num) hx.1⟩)
    exact h1_c.comp (f := fun x => (-(ψ (g x) - c).re, F Complex.I (-(ψ (g x) - c).im) x))
      ((Complex.continuous_re.comp_continuousOn hwc).neg.prodMk hin)
      (fun x hx => ⟨hneg _ (hw _ hx.2).1, (hI 1 x hx.1 _ (hneg _ (hw _ hx.2).2)).1⟩)
  set Ub : Set Z := Ω 4 ∩ g ⁻¹' {b} with hUb
  set U : Set Z := (Ω 2 ∩ g ⁻¹' Δ) ∩ Gf ⁻¹' Ω 4 with hU
  have hUo : IsOpen U :=
    hGc.isOpen_inter_preimage ((hΩo 2).inter (hΔo.preimage hgc)) (hΩo 4)
  have hpΔ : Continuous (fun p : Ub × Δ => ψ (p.2 : B)) :=
    ψ.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_snd)
      (fun p => p.2.2.1)
  have hinner : Continuous (fun p : Ub × Δ => F 1 (ψ (p.2 : B) - c).re (p.1 : Z)) :=
    h1_c.comp_continuous (f := fun p : Ub × Δ => ((ψ (p.2 : B) - c).re, (p.1 : Z)))
      ((Complex.continuous_re.comp (hpΔ.sub continuous_const)).prodMk
        (continuous_subtype_val.comp continuous_fst))
      (fun p => ⟨(hw _ p.2.2).1, hanti (by norm_num) p.1.2.1⟩)
  have hΦc : Continuous (fun p : Ub × Δ => Φf p.1 p.2) :=
    hI_c.comp_continuous
      (f := fun p : Ub × Δ => ((ψ (p.2 : B) - c).im, F 1 (ψ (p.2 : B) - c).re (p.1 : Z)))
      ((Complex.continuous_im.comp (hpΔ.sub continuous_const)).prodMk hinner)
      (fun p => ⟨(hw _ p.2.2).2, hanti (by norm_num) (h1 3 _ p.1.2.1 _ (hw _ p.2.2).1).1⟩)
  have hfwd' : ∀ p : Ub × Δ, _ := fun p => hfwd p.1 p.1.2.1 p.1.2.2 p.2 p.2.2
  have hmemU : ∀ p : Ub × Δ, Φf p.1 p.2 ∈ U := fun p => by
    obtain ⟨h1', h2', h3', -⟩ := hfwd' p
    exact ⟨⟨h1', by rw [mem_preimage, h2']; exact p.2.2⟩, by rw [mem_preimage, h3']; exact p.1.2.1⟩
  have hbwd' : ∀ x : U, _ := fun x : U => hbwd x x.2.1.1 x.2.1.2
  let Φ : Ub × Δ ≃ₜ U :=
    { toFun := fun p => ⟨Φf p.1 p.2, hmemU p⟩
      invFun := fun x => (⟨Gf x, x.2.2, (hbwd' x).2.1⟩, ⟨g x, x.2.1.2⟩)
      left_inv := fun p => Prod.ext (Subtype.ext (hfwd' p).2.2.1) (Subtype.ext (hfwd' p).2.1)
      right_inv := fun x => Subtype.ext (hbwd' x).2.2.1
      continuous_toFun := hΦc.subtype_mk _
      continuous_invFun :=
        ((hGc.comp_continuous continuous_subtype_val (fun x => x.2.1)).subtype_mk _).prodMk
          ((hgc.comp continuous_subtype_val).subtype_mk _) }
  refine ⟨Ub, U, hb, inter_subset_right, ⟨Ω 4, hΩo 4, rfl⟩, ?_, hUo,
    fun x hx => hx.1.2, ?_, Φ, fun p => (hfwd' p).2.1, ?_, fun i p => (hfwd' p).2.2.2 i⟩
  · exact fun x hx => ⟨hEΩ' 4 le_rfl ⟨hx.1, mem_preimage.mpr ((hx.2 : g x = b) ▸ hb)⟩, hx.2⟩
  · intro x hx
    have hx2 : x ∈ Ω 2 := hEΩ' 2 (by norm_num) hx
    obtain ⟨-, hgG, -, hDG⟩ := hbwd x hx2 hx.2
    refine ⟨⟨hx2, hx.2⟩, hEΩ' 4 le_rfl ⟨?_, mem_preimage.mpr (hgG ▸ hb)⟩⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
    exact mem_iUnion.mpr ⟨i, (hDG i).mpr hi⟩
  · intro z
    change F Complex.I (ψ b - c).im (F 1 (ψ b - c).re (z : Z)) = z
    have hz0 : (z : Z) ∈ Ω 0 := hanti (by norm_num) z.2.1
    rw [← hc, sub_self, Complex.zero_re, Complex.zero_im, h1_0 _ hz0, hI_0 _ hz0]

/-- **Product germ along a proper relative SNC divisor.** Let `g : Z → B` be holomorphic from a
Hausdorff second countable complex manifold of dimension `n` to a complex curve, and let `D` be
the components of a closed SNC divisor `E = ⋃ i, D i` proper over `B`, such that `g` is a
submersion near `E` and on every stratum of `E`. Then for every `b ∈ B` and every neighbourhood
`N` of `b` there are a coordinate disk `Δ ⊆ N` about `b`, an open neighbourhood `U_b` of `E_b` in
the fibre `g⁻¹{b}`, an open neighbourhood `U` of `E_Δ` in `g⁻¹ Δ`, and a homeomorphism
`Φ : U_b × Δ ≃ₜ U` over `Δ`, which is the identity over `b` and preserves every `D i`. -/
@[mmp "lem_mmp_relative_snc_horizontal_product_germ"]
public theorem exists_homeomorph_prod_of_relativeSNC
    {n : ℕ} {Z B : Type*} [TopologicalSpace Z] [T2Space Z] [SecondCountableTopology Z]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) Z]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z]
    [TopologicalSpace B] [T2Space B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ∞ B]
    {g : Z → B} (hg : MDifferentiable 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g)
    {ι : Type*} {D : ι → Set Z}
    (hD : ∀ x : Z, ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z,
      x ∈ φ.source ∧ ∃ (s : Finset ι) (c : s ↪ Fin n),
        (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
        ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0})
    (_hE : IsClosed (⋃ i, D i))
    (hproper : IsProperMap (fun x : (⋃ i, D i : Set Z) => g x))
    (hsubmersion : ∃ W : Set Z, IsOpen W ∧ (⋃ i, D i) ⊆ W ∧
      ∀ x ∈ W, Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x))
    (hstrata : ∀ x ∈ ⋃ i, D i, ∃ v ∈ tangentConeAt ℂ
        ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).target ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).symm ⁻¹' ⋂ (i) (_ : x ∈ D i), D i)
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x),
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x v ≠ 0)
    (b : B) {N : Set B} (hN : N ∈ 𝓝 b) :
    ∃ ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ B, b ∈ ψ.source ∧ ∃ r : ℝ, 0 < r ∧
      Metric.ball (ψ b) r ⊆ ψ.target ∧
      let Δ : Set B := ψ.source ∩ ψ ⁻¹' Metric.ball (ψ b) r
      Δ ⊆ N ∧ ∃ (Ub U : Set Z) (hb : b ∈ Δ),
        Ub ⊆ g ⁻¹' {b} ∧ (∃ O : Set Z, IsOpen O ∧ Ub = O ∩ g ⁻¹' {b}) ∧
        (⋃ i, D i) ∩ g ⁻¹' {b} ⊆ Ub ∧
        IsOpen U ∧ U ⊆ g ⁻¹' Δ ∧ (⋃ i, D i) ∩ g ⁻¹' Δ ⊆ U ∧
        ∃ Φ : Ub × Δ ≃ₜ U,
          (∀ p : Ub × Δ, g (Φ p) = p.2) ∧
          (∀ z : Ub, (Φ (z, ⟨b, hb⟩) : Z) = z) ∧
          ∀ (i : ι) (p : Ub × Δ), (Φ p : Z) ∈ D i ↔ (p.1 : Z) ∈ D i := by
  set ψ := chartAt ℂ b
  have hT : ψ.target ∩ ψ.symm ⁻¹' N ∈ 𝓝 (ψ b) := by
    refine inter_mem (ψ.open_target.mem_nhds (ψ.map_source (mem_chart_source ℂ b))) ?_
    refine (ψ.continuousAt_symm (ψ.map_source (mem_chart_source ℂ b))).preimage_mem_nhds ?_
    rwa [ψ.left_inv (mem_chart_source ℂ b)]
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r ≤ ε := Ioc_mem_nhdsGT hε
  obtain ⟨r, ⟨hr0, hrε⟩, hcore⟩ := (hsmall.and
    (eventually_exists_homeomorph_prod_ball hg hD hproper hsubmersion hstrata b)).exists
  refine ⟨ψ, IsManifold.chart_mem_maximalAtlas b, mem_chart_source ℂ b, r, hr0,
    fun y hy => (hεT (Metric.ball_subset_ball hrε hy)).1, ?_, hcore⟩
  intro x hx
  have := (hεT (Metric.ball_subset_ball hrε hx.2)).2
  rwa [mem_preimage, ψ.left_inv hx.1] at this

end MMP.Analytic
