module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.ChartForms
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ChartStalkBasis

/-!
# Logarithmic forms at the points of a chart

Let `W` be a chart of the relative simple normal crossing divisor `D` on an integral scheme `Y`
over `k`, and `y ∈ W'` a point of the chart.

* Off `D`, the local equations `tᵢ` of the components of `D` are units at `y`, so the rational
  chart forms `tᵢ⁻¹ dtᵢ` and `dtᵢ` lie in the image of `Ω_{𝒪_{Y,y}/k}`: the rational form, in
  `k(Y)`, of a logarithmic form on the chart lies in the wedges of the image of `Ω_{𝒪_{Y,y}/k}`.
* Off every component other than `j i₀`, with equation `σ`, the chart coordinates with `σ` first
  give an adapted basis `dσ, dy₁, …, dyₘ` of `Ω_{𝒪_{Y,y}/k}`, and the rational chart forms lie in
  the span of `σ⁻¹ dσ, dy₁, …, dyₘ`; a section of `Ω^p(log D)(-D)` has rational form `σ η` with `η`
  in the wedges of that span.

These are the lattices `Λ_reg` and `σ Λ_log` at the points of a cover over a prime divisor which
enter the tame trace estimate.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.isUnit_germ_of_notMem_support`: local equations are
  units off the divisor.
* `MMP.FourfoldProofs.FractionalLogComplexProof.openFormsMap_ratForm_mem_wedgeSpan_regular`: the
  regular lattice off the divisor.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_basis_cons_chartForm_mem_span`: the adapted
  basis on a component.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_openFormsMap_ratForm_eq_smul_log`: the twisted
  logarithmic lattice on a component.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

/-- **A local equation of a prime divisor is a unit off the divisor.** If `t` generates the ideal
of `E` on `W` and `y ∈ W` is not on `E`, then the germ of `t` at `y` is a unit. -/
theorem isUnit_germ_of_notMem_support {Y : Scheme.{u}} (E : MMP.Mori.PrimeDivisor Y)
    (W : Y.affineOpens) {t : Γ(Y, W)} (ht : E.idealSheaf.ideal W = Ideal.span {t}) {y : Y}
    (hy : y ∈ (W : Y.Opens)) (hyE : y ∉ E.support) :
    IsUnit (Y.presheaf.germ (W : Y.Opens) y hy t) := by
  have h1 : y ∉ E.idealSheaf.support := hyE
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hy, ht, Scheme.mem_zeroLocus_iff] at h1
  push Not at h1
  obtain ⟨a, ha, hya⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [Scheme.basicOpen_mul] at hya
  exact (Y.mem_basicOpen _ _ hy).1 hya.2

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- **The regular lattice off the chart components.** At a point `y ∈ W'` lying on none of the
components `j i`, the rational form in `k(Y)` of a combination of the chart basis lies in the wedges
of the span of the image of a basis `bR` of `Ω_{𝒪_{Y,y}/k}`. -/
theorem openFormsMap_ratForm_mem_wedgeSpan_regular [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    (D : MMP.Mori.Divisor Y) [Nonempty (cU D)] {n : ℕ} (W : Y.affineOpens)
    (t : Fin n → Γ(Y, W)) {r : ℕ} (hr : r ≤ n) (j : Fin r → MMP.Mori.PrimeDivisor Y)
    (hjD : ∀ i, (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : Y.Opens)))
    (hs : ∀ i, s i * (cU D).ι.app W (t (Fin.castLE hr i)) = 1)
    (θ : Fin n → (TB ((cU D).ι ≫ f)).Total (op ((cU D).ι ⁻¹ᵁ (W : Y.Opens))))
    (hθ : θ = fun i : Fin n => if h : (i : ℕ) < r then
        sm ((cU D).ι ≫ f) _ (s ⟨i, h⟩) * δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i))
      else δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i)))
    (p : ℕ) (W' : Y.affineOpens) (hW' : (W' : Y.Opens) ≤ W)
    (c : {K : Finset (Fin n) // K.card = p} → Γ(Y, W'))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ (W' : Y.Opens))))
    (hω : (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω =
      ∑ K, sm ((cU D).ι ≫ f) _ (((cU D).ι.app W').hom (c K)) *
        ((K.1.sort (· ≤ ·)).map fun i =>
          (TB ((cU D).ι ≫ f)).totalRestrict
            ((Opens.map (cU D).ι.base).map (homOfLE hW')).op (θ i)).prod)
    (O : (cU D).toScheme.affineOpens)
    (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W' : Y.Opens))
    [Nonempty (O : (cU D).toScheme.Opens)] {y : Y} (hy : y ∈ (W' : Y.Opens))
    (hyD : ∀ i, y ∉ (j i).support) {ι : Type*}
    (bR : letI := MMP.Mori.stalkAlgebra f y
      Module.Basis ι (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k]) :
    letI := MMP.Mori.functionFieldAlgebra f
    letI := MMP.Mori.stalkAlgebra f y
    haveI := MMP.Mori.isScalarTower_stalk_functionField f y
    openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
        ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op ω)) ∈
      wedgeSpan (Y.presheaf.stalk y) (Submodule.span (Y.presheaf.stalk y)
        (Set.range (KaehlerDifferential.map k k (Y.presheaf.stalk y) Y.functionField ∘ bR))) p := by
  have : Nonempty (W' : Y.Opens) := ⟨⟨y, hy⟩⟩
  have : Nonempty (W : Y.Opens) := ⟨⟨y, hW' hy⟩⟩
  let := MMP.Mori.functionFieldAlgebra f
  let := MMP.Mori.stalkAlgebra f y
  have := MMP.Mori.isScalarTower_stalk_functionField f y
  refine wedgeSpan_mono ?_ p
    (openFormsMap_ratForm_mem_wedgeSpan f D W t hr s hs θ hθ p W' hW' c ω hω O hO hy)
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hyW : y ∈ (W : Y.Opens) := hW' hy
  have hD : KaehlerDifferential.D k Y.functionField (Y.germToFunctionField W (t i)) ∈
      Submodule.span (Y.presheaf.stalk y)
        (Set.range (KaehlerDifferential.map k k (Y.presheaf.stalk y) Y.functionField ∘ bR)) := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hyW,
      ← KaehlerDifferential.map_D k k (Y.presheaf.stalk y) Y.functionField]
    exact map_mem_span_of_basis k bR _
  unfold chartForm
  split_ifs with h
  · have hu : IsUnit (Y.presheaf.germ (W : Y.Opens) y hyW (t i)) :=
      isUnit_germ_of_notMem_support (j ⟨i, h⟩) W (hjD ⟨i, h⟩) hyW (hyD ⟨i, h⟩)
    have hinv : (Y.germToFunctionField W (t i))⁻¹ =
        algebraMap (Y.presheaf.stalk y) Y.functionField (↑hu.unit⁻¹ : Y.presheaf.stalk y) := by
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hyW, map_units_inv,
        IsUnit.unit_spec]
    rw [hinv, algebraMap_smul]
    exact Submodule.smul_mem _ _ hD
  · rw [one_smul]
    exact hD

/-- **An adapted basis at a point off the other components.** At a point `y ∈ W` lying on no
component `j i` with `i ≠ i₀`, the chart coordinates, reordered so the equation of `j i₀` comes
first, give a basis `dσ, dy₁, …, dyₘ` of `Ω_{𝒪_{Y,y}/k}`, and every rational chart form lies in the
`𝒪_{Y,y}`-span of the logarithmic forms `σ⁻¹ dσ, dy₁, …, dyₘ`. -/
theorem exists_basis_cons_chartForm_mem_span [IsIntegral Y] (f : Y ⟶ Spec (.of k)) {n : ℕ}
    (W : Y.affineOpens) (V : (Spec (.of k)).affineOpens)
    (e : (W : Y.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens)) (t : Fin n → Γ(Y, W))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(Y, W) Ω[Γ(Y, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(Y, W) (t i))
    {r : ℕ} (hr : r ≤ n) (j : Fin r → MMP.Mori.PrimeDivisor Y)
    (hjD : ∀ i, (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    {y : Y} (hy : y ∈ (W : Y.Opens)) (i₀ : Fin r) (hother : ∀ i, i ≠ i₀ → y ∉ (j i).support) :
    haveI : Nonempty (W : Y.Opens) := ⟨⟨y, hy⟩⟩
    letI := MMP.Mori.functionFieldAlgebra f
    letI := MMP.Mori.stalkAlgebra f y
    haveI := MMP.Mori.isScalarTower_stalk_functionField f y
    ∃ (m : ℕ) (σe : Fin (m + 1) ≃ Fin n) (bR : Module.Basis (Fin (m + 1)) (Y.presheaf.stalk y)
        Ω[Y.presheaf.stalk y⁄k]),
      σe 0 = Fin.castLE hr i₀ ∧
      (∀ i, bR i = KaehlerDifferential.D k (Y.presheaf.stalk y)
        ((Fin.cons (Y.presheaf.germ (W : Y.Opens) y hy (t (Fin.castLE hr i₀)))
          fun l => Y.presheaf.germ (W : Y.Opens) y hy (t (σe l.succ)) :
            Fin (m + 1) → Y.presheaf.stalk y) i)) ∧
      ∀ i, chartForm f W t r i ∈ Submodule.span (Y.presheaf.stalk y) (Set.range
        (Fin.cons ((Y.germToFunctionField W (t (Fin.castLE hr i₀)))⁻¹ •
            KaehlerDifferential.D k Y.functionField
              (Y.germToFunctionField W (t (Fin.castLE hr i₀))))
          fun l => KaehlerDifferential.D k Y.functionField (Y.germToFunctionField W (t (σe l.succ)))
          : Fin (m + 1) → Ω[Y.functionField⁄k])) := by
  have : Nonempty (W : Y.Opens) := ⟨⟨y, hy⟩⟩
  let := MMP.Mori.functionFieldAlgebra f
  let := MMP.Mori.stalkAlgebra f y
  have := MMP.Mori.isScalarTower_stalk_functionField f y
  set i₀' : Fin n := Fin.castLE hr i₀
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by
    have := i₀'.2; omega)
  let c0 : Fin (m + 1) ≃ Fin n := finCongr hm.symm
  let σe : Fin (m + 1) ≃ Fin n := (Equiv.swap 0 (c0.symm i₀')).trans c0
  have hσ0 : σe 0 = i₀' := by simp [σe]
  obtain ⟨b0, hb0⟩ := exists_basis_D_stalk_of_chart f W V e t hb hy
  refine ⟨m, σe, b0.reindex σe.symm, hσ0, fun i => ?_, fun i => ?_⟩
  · rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb0]
    refine Fin.cases ?_ (fun l => ?_) i
    · rw [Fin.cons_zero, hσ0]
    · rw [Fin.cons_succ]
  · have hD : ∀ l : Fin m, KaehlerDifferential.D k Y.functionField
        (Y.germToFunctionField W (t (σe l.succ))) ∈ Submodule.span (Y.presheaf.stalk y) (Set.range
          (Fin.cons ((Y.germToFunctionField W (t i₀'))⁻¹ •
            KaehlerDifferential.D k Y.functionField (Y.germToFunctionField W (t i₀')))
          fun l => KaehlerDifferential.D k Y.functionField (Y.germToFunctionField W (t (σe l.succ)))
          : Fin (m + 1) → Ω[Y.functionField⁄k])) := fun l =>
      Submodule.subset_span ⟨l.succ, by rw [Fin.cons_succ]⟩
    by_cases hi : i = i₀'
    · subst hi
      unfold chartForm
      simp only [show ((i₀' : Fin n) : ℕ) < r from i₀.2, ite_true]
      exact Submodule.subset_span ⟨0, by rw [Fin.cons_zero]⟩
    · have hne : σe.symm i ≠ 0 := fun h0 => hi (by rw [← hσ0, ← h0, Equiv.apply_symm_apply])
      obtain ⟨l, hl⟩ := Fin.exists_succ_eq.2 hne
      have hil : i = σe l.succ := by rw [hl, Equiv.apply_symm_apply]
      unfold chartForm
      split_ifs with h
      · have hni : (⟨i, h⟩ : Fin r) ≠ i₀ := fun h' => hi (Fin.ext (by
          rw [show ((i₀' : Fin n) : ℕ) = (i₀ : ℕ) from rfl, ← h']))
        have hu : IsUnit (Y.presheaf.germ (W : Y.Opens) y hy (t i)) :=
          isUnit_germ_of_notMem_support (j ⟨i, h⟩) W (hjD ⟨i, h⟩) hy (hother _ hni)
        have hinv : (Y.germToFunctionField W (t i))⁻¹ =
            algebraMap (Y.presheaf.stalk y) Y.functionField (↑hu.unit⁻¹ : Y.presheaf.stalk y) := by
          rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hy, map_units_inv,
            IsUnit.unit_spec]
        rw [hinv, algebraMap_smul]
        refine Submodule.smul_mem _ _ ?_
        rw [hil]
        exact hD l
      · rw [one_smul, hil]
        exact hD l

/-- **The twisted logarithmic lattice off the other components.** Let `y ∈ W'` lie on no component
`j i` of `D` with `i ≠ i₀`. The rational form in `k(Y)` of a section of
`Ω^p(log D)(-D)` on the chart is `σ η`, `σ` the local equation of `j i₀` at `y`, with `η` in the
wedges of the `𝒪_{Y,y}`-span of the logarithmic forms `σ⁻¹ dσ, dy₁, …, dyₘ` of an adapted basis
`dσ, dy₁, …, dyₘ` of `Ω_{𝒪_{Y,y}/k}`. -/
theorem exists_openFormsMap_ratForm_eq_smul_log [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    (D : MMP.Mori.Divisor Y) [Nonempty (cU D)] {n : ℕ} (W : Y.affineOpens)
    (V : (Spec (.of k)).affineOpens) (e : (W : Y.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens))
    (t : Fin n → Γ(Y, W))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(Y, W) Ω[Γ(Y, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(Y, W) (t i))
    {r : ℕ} (hr : r ≤ n) (j : Fin r → MMP.Mori.PrimeDivisor Y)
    (hjD : ∀ i, (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (hDW : D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)})
    (s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : Y.Opens)))
    (hs : ∀ i, s i * (cU D).ι.app W (t (Fin.castLE hr i)) = 1)
    (θ : Fin n → (TB ((cU D).ι ≫ f)).Total (op ((cU D).ι ⁻¹ᵁ (W : Y.Opens))))
    (hθ : θ = fun i : Fin n => if h : (i : ℕ) < r then
        sm ((cU D).ι ≫ f) _ (s ⟨i, h⟩) * δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i))
      else δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i)))
    (p : ℕ) (W' : Y.affineOpens) (hW' : (W' : Y.Opens) ≤ W)
    (c : {K : Finset (Fin n) // K.card = p} → Γ(Y, W'))
    (hc : ∀ K, c K ∈ D.suppIdeal.ideal W')
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ (W' : Y.Opens))))
    (hω : (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω =
      ∑ K, sm ((cU D).ι ≫ f) _ (((cU D).ι.app W').hom (c K)) *
        ((K.1.sort (· ≤ ·)).map fun i =>
          (TB ((cU D).ι ≫ f)).totalRestrict
            ((Opens.map (cU D).ι.base).map (homOfLE hW')).op (θ i)).prod)
    (O : (cU D).toScheme.affineOpens)
    (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W' : Y.Opens))
    [Nonempty (O : (cU D).toScheme.Opens)] {y : Y} (hy : y ∈ (W' : Y.Opens)) (i₀ : Fin r)
    (hother : ∀ i, i ≠ i₀ → y ∉ (j i).support) :
    letI := MMP.Mori.functionFieldAlgebra f
    letI := MMP.Mori.stalkAlgebra f y
    haveI := MMP.Mori.isScalarTower_stalk_functionField f y
    ∃ (m : ℕ) (yv : Fin m → Y.presheaf.stalk y) (bR : Module.Basis (Fin (m + 1))
        (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k]),
      (∀ i, bR i = KaehlerDifferential.D k (Y.presheaf.stalk y)
        ((Fin.cons (Y.presheaf.germ (W : Y.Opens) y (hW' hy) (t (Fin.castLE hr i₀))) yv :
            Fin (m + 1) → Y.presheaf.stalk y) i)) ∧
      ∃ η ∈ wedgeSpan (Y.presheaf.stalk y) (Submodule.span (Y.presheaf.stalk y) (Set.range
          (Fin.cons ((algebraMap (Y.presheaf.stalk y) Y.functionField
              (Y.presheaf.germ (W : Y.Opens) y (hW' hy) (t (Fin.castLE hr i₀))))⁻¹ •
              KaehlerDifferential.D k Y.functionField (algebraMap (Y.presheaf.stalk y)
                Y.functionField (Y.presheaf.germ (W : Y.Opens) y (hW' hy) (t (Fin.castLE hr i₀)))))
            fun l => KaehlerDifferential.D k Y.functionField
              (algebraMap (Y.presheaf.stalk y) Y.functionField (yv l))
            : Fin (m + 1) → Ω[Y.functionField⁄k]))) p,
        openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
            ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op ω)) =
          algebraMap (Y.presheaf.stalk y) Y.functionField
            (Y.presheaf.germ (W : Y.Opens) y (hW' hy) (t (Fin.castLE hr i₀))) • η := by
  classical
  have hyW : y ∈ (W : Y.Opens) := hW' hy
  have : Nonempty (W' : Y.Opens) := ⟨⟨y, hy⟩⟩
  have : Nonempty (W : Y.Opens) := ⟨⟨y, hyW⟩⟩
  let := MMP.Mori.functionFieldAlgebra f
  let := MMP.Mori.stalkAlgebra f y
  have := MMP.Mori.isScalarTower_stalk_functionField f y
  obtain ⟨m, σe, bR, hσ0, hbR, hspan⟩ :=
    exists_basis_cons_chartForm_mem_span f W V e t hb hr j hjD hyW i₀ hother
  have hgerm : ∀ a : Γ(Y, W), Y.germToFunctionField W a =
      algebraMap (Y.presheaf.stalk y) Y.functionField (Y.presheaf.germ (W : Y.Opens) y hyW a) :=
    fun a => (Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hyW a).symm
  refine ⟨m, fun l => Y.presheaf.germ (W : Y.Opens) y hyW (t (σe l.succ)), bR, hbR, ?_⟩
  simp only [hgerm] at hspan
  have hcK : ∀ K, ∃ ρ : Y.presheaf.stalk y, Y.germToFunctionField W' (c K) =
      algebraMap (Y.presheaf.stalk y) Y.functionField
        (Y.presheaf.germ (W : Y.Opens) y hyW (t (Fin.castLE hr i₀))) *
        algebraMap (Y.presheaf.stalk y) Y.functionField ρ := by
    intro K
    have h1 := hc K
    rw [← Scheme.IdealSheafData.map_ideal D.suppIdeal hW', hDW, Ideal.map_span,
      Set.image_singleton, Ideal.mem_span_singleton'] at h1
    obtain ⟨a, ha⟩ := h1
    refine ⟨Y.presheaf.germ (W' : Y.Opens) y hy a *
      ∏ i ∈ Finset.univ.erase i₀, Y.presheaf.germ (W : Y.Opens) y hyW (t (Fin.castLE hr i)), ?_⟩
    rw [← ha, ← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hy, ← map_mul]
    congr 1
    rw [map_mul]
    erw [TopCat.Presheaf.germ_res_apply]
    rw [map_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    ring
  choose ρ hρ using hcK
  refine ⟨∑ K : {K : Finset (Fin n) // K.card = p}, ρ K •
      exteriorPower.ιMulti Y.functionField p fun l => chartForm f W t r (K.1.orderEmbOfFin K.2 l),
    Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (ιMulti_mem_wedgeSpan fun l => hspan _),
    ?_⟩
  rw [openFormsMap_ratForm_eq_sum f D W t hr s hs θ hθ p W' hW' c ω hω O hO, Finset.smul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [hρ K, ← smul_smul, algebraMap_smul]
  simp only [algebraMap_smul]

end MMP.FourfoldProofs.FractionalLogComplexProof
