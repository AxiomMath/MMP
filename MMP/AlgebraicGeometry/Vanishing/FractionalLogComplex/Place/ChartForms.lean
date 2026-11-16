module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ChartLogFormRationalForm
public import MMP.AlgebraicGeometry.FunctionField.OpenSubscheme
public import MMP.RingTheory.Kaehler.WedgeSpan

/-!
# Logarithmic forms on a chart, at the points of the chart

Let `W` be a chart of the relative simple normal crossing divisor `D` on an integral scheme `Y`
over `k`, with coordinates `tᵢ`, and `ω` a form on `W' ∖ D`, `W' ⊆ W`, equal to a combination
`∑_K c_K θ_K` of the chart basis. Moved to the function field `k(Y)`, its rational form is
`∑_K c_K β_K`, the `β_K` wedges of the `βᵢ = tᵢ⁻¹ dtᵢ` (`i < r`) and `βᵢ = dtᵢ` (`i ≥ r`). At
every point `y ∈ W'` it therefore lies in the `𝒪_{Y,y}`-span of the wedges of the `βᵢ`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.openFormsMap_ratForm_eq_sum`: the rational form in
  `k(Y)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.openFormsMap_ratForm_mem_wedgeSpan`: the local lattice
  at a point of the chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

/-- The germ at the generic point is unchanged by restriction. -/
theorem germToFunctionField_map {Y : Scheme.{u}} [IsIntegral Y] {O O' : Y.Opens} (h : O ≤ O')
    [Nonempty O] [Nonempty O'] (a : Γ(Y, O')) :
    Y.germToFunctionField O (Y.presheaf.map (homOfLE h).op a) = Y.germToFunctionField O' a :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ a

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- The rational chart form `tᵢ⁻¹ dtᵢ` (`i < r`), resp. `dtᵢ` (`i ≥ r`), in `k(Y)`. -/
noncomputable def chartForm [IsIntegral Y] (f : Y ⟶ Spec (.of k)) {n : ℕ} (W : Y.affineOpens)
    [Nonempty (W : Y.Opens)] (t : Fin n → Γ(Y, W)) (r : ℕ) (i : Fin n) :
    letI := MMP.Mori.functionFieldAlgebra f
    Ω[Y.functionField⁄k] :=
  letI := MMP.Mori.functionFieldAlgebra f
  (if (i : ℕ) < r then (Y.germToFunctionField W (t i))⁻¹ else 1) •
    D k Y.functionField (Y.germToFunctionField W (t i))

/-- For `i < r` the rational chart form is the logarithmic form `tᵢ⁻¹ dtᵢ`. -/
theorem chartForm_of_lt [IsIntegral Y] (f : Y ⟶ Spec (.of k)) {n : ℕ} (W : Y.affineOpens)
    [Nonempty (W : Y.Opens)] (t : Fin n → Γ(Y, W)) {r : ℕ} {i : Fin n} (h : (i : ℕ) < r) :
    letI := MMP.Mori.functionFieldAlgebra f
    chartForm f W t r i =
      (Y.germToFunctionField W (t i))⁻¹ • D k Y.functionField (Y.germToFunctionField W (t i)) := by
  rw [chartForm, if_pos h]

/-- For `r ≤ i` the rational chart form is the exact form `dtᵢ`. -/
theorem chartForm_of_le [IsIntegral Y] (f : Y ⟶ Spec (.of k)) {n : ℕ} (W : Y.affineOpens)
    [Nonempty (W : Y.Opens)] (t : Fin n → Γ(Y, W)) {r : ℕ} {i : Fin n} (h : r ≤ (i : ℕ)) :
    letI := MMP.Mori.functionFieldAlgebra f
    chartForm f W t r i = D k Y.functionField (Y.germToFunctionField W (t i)) := by
  rw [chartForm, if_neg h.not_gt, one_smul]

/-- `openFormsMap` on a wedge of multiples of exact forms. -/
theorem openFormsMap_ιMulti_smul_D [IsIntegral Y] (U : Y.Opens) [Nonempty U]
    (sY : Y ⟶ Spec (.of k)) (q : ℕ) (a x : Fin q → U.toScheme.functionField) :
    letI := MMP.Mori.functionFieldAlgebra sY
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
    openFormsMap U sY q
        (exteriorPower.ιMulti U.toScheme.functionField q
          fun j => a j • KaehlerDifferential.D k U.toScheme.functionField (x j)) =
      exteriorPower.ιMulti Y.functionField q fun j =>
        openFunctionFieldEquiv U (a j) •
          KaehlerDifferential.D k Y.functionField (openFunctionFieldEquiv U (x j)) := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  let := openFunctionFieldAlgebra U
  have := isScalarTower_openFunctionField U sY
  refine (KaehlerDifferential.mapExteriorPower_ιMulti k U.toScheme.functionField Y.functionField
    q _).trans ?_
  congr 1
  funext j
  rw [LinearMap.map_smul_of_tower, KaehlerDifferential.map_D,
    algebra_compatible_smul Y.functionField]
  rfl

/-- **The rational form of a combination of the chart basis, in `k(Y)`.** -/
theorem openFormsMap_ratForm_eq_sum [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    (D : MMP.Mori.Divisor Y) [Nonempty (cU D)] {n : ℕ} (W : Y.affineOpens)
    (t : Fin n → Γ(Y, W)) {r : ℕ} (hr : r ≤ n)
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
    [Nonempty (O : (cU D).toScheme.Opens)] [Nonempty (W : Y.Opens)] [Nonempty (W' : Y.Opens)] :
    letI := MMP.Mori.functionFieldAlgebra f
    openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
        ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op ω)) =
      ∑ K : {K : Finset (Fin n) // K.card = p}, Y.germToFunctionField W' (c K) •
        exteriorPower.ιMulti Y.functionField p fun j =>
          chartForm f W t r (K.1.orderEmbOfFin K.2 j) := by
  let := MMP.Mori.functionFieldAlgebra f
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  have hO' : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W : Y.Opens) :=
    hO.trans (Scheme.Hom.preimage_mono _ hW')
  have : Nonempty ((cU D).ι ⁻¹ᵁ (W' : Y.Opens)) := by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (O : (cU D).toScheme.Opens)›
    exact ⟨⟨z, hO hz⟩⟩
  have : Nonempty ((cU D).ι ⁻¹ᵁ (W : Y.Opens)) := by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (O : (cU D).toScheme.Opens)›
    exact ⟨⟨z, hO' hz⟩⟩
  have hg : ∀ {Q : Y.Opens} (hQ : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ Q) [Nonempty Q]
      [Nonempty ((cU D).ι ⁻¹ᵁ Q)] (a : Γ(Y, Q)),
      openFunctionFieldEquiv (cU D) ((cU D).toScheme.germToFunctionField O
        ((cU D).toScheme.presheaf.map (homOfLE hQ).op ((cU D).ι.app Q a))) =
      Y.germToFunctionField Q a := by
    intro Q hQ _ _ a
    rw [germToFunctionField_map hQ, openFunctionFieldEquiv_germ]
  rw [ratForm_eq_sum_ιMulti_of_incl_eq_combo f D W t hr s hs θ hθ p W' hW' c ω hω O hO, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [openFormsMap_smul, hg hO]
  congr 1
  have hfam : (fun j => if ((K.1.orderEmbOfFin K.2 j : Fin n) : ℕ) < r then
        ((cU D).toScheme.germToFunctionField O
          ((cU D).toScheme.presheaf.map (homOfLE hO').op
            ((cU D).ι.app W (t (K.1.orderEmbOfFin K.2 j)))))⁻¹ •
          KaehlerDifferential.D k (cU D).toScheme.functionField
            ((cU D).toScheme.germToFunctionField O
              ((cU D).toScheme.presheaf.map (homOfLE hO').op
                ((cU D).ι.app W (t (K.1.orderEmbOfFin K.2 j)))))
      else KaehlerDifferential.D k (cU D).toScheme.functionField
        ((cU D).toScheme.germToFunctionField O
          ((cU D).toScheme.presheaf.map (homOfLE hO').op
            ((cU D).ι.app W (t (K.1.orderEmbOfFin K.2 j)))))) =
      fun j => (if ((K.1.orderEmbOfFin K.2 j : Fin n) : ℕ) < r then
        ((cU D).toScheme.germToFunctionField O
          ((cU D).toScheme.presheaf.map (homOfLE hO').op
            ((cU D).ι.app W (t (K.1.orderEmbOfFin K.2 j)))))⁻¹ else 1) •
          KaehlerDifferential.D k (cU D).toScheme.functionField
            ((cU D).toScheme.germToFunctionField O
              ((cU D).toScheme.presheaf.map (homOfLE hO').op
                ((cU D).ι.app W (t (K.1.orderEmbOfFin K.2 j))))) := by
    funext j
    split_ifs <;> simp
  rw [hfam, openFormsMap_ιMulti_smul_D]
  congr 1
  funext j
  split_ifs with h
  · rw [chartForm_of_lt f W t h, map_inv₀, hg hO']
  · rw [chartForm_of_le f W t (not_lt.mp h), map_one, one_smul, hg hO']

/-- **The local lattice at a point of the chart.** At every point `y ∈ W'`, the rational form in
`k(Y)` of a combination of the chart basis lies in the `𝒪_{Y,y}`-span of the wedges of the
rational chart forms. -/
theorem openFormsMap_ratForm_mem_wedgeSpan [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    (D : MMP.Mori.Divisor Y) [Nonempty (cU D)] {n : ℕ} (W : Y.affineOpens)
    (t : Fin n → Γ(Y, W)) {r : ℕ} (hr : r ≤ n)
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
    [Nonempty (O : (cU D).toScheme.Opens)] {y : Y} (hy : y ∈ (W' : Y.Opens)) :
    haveI : Nonempty (W' : Y.Opens) := ⟨⟨y, hy⟩⟩
    haveI : Nonempty (W : Y.Opens) := ⟨⟨y, hW' hy⟩⟩
    letI := MMP.Mori.functionFieldAlgebra f
    openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
        ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op ω)) ∈
      wedgeSpan (Y.presheaf.stalk y)
        (Submodule.span (Y.presheaf.stalk y) (Set.range (chartForm f W t r))) p := by
  have : Nonempty (W' : Y.Opens) := ⟨⟨y, hy⟩⟩
  have : Nonempty (W : Y.Opens) := ⟨⟨y, hW' hy⟩⟩
  let := MMP.Mori.functionFieldAlgebra f
  rw [openFormsMap_ratForm_eq_sum f D W t hr s hs θ hθ p W' hW' c ω hω O hO]
  refine Submodule.sum_mem _ fun K _ => ?_
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hy, algebraMap_smul]
  exact Submodule.smul_mem _ _ (ιMulti_mem_wedgeSpan fun j => Submodule.subset_span ⟨_, rfl⟩)

end MMP.FourfoldProofs.FractionalLogComplexProof
