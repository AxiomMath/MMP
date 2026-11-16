module

public import MMP.AlgebraicTopology.BorelMoore.PushforwardSheets
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.CycleClassPushforwardOrientation
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVarietyUnique
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreVanishing
public import MMP.AlgebraicTopology.FundamentalClass.Homeomorphism
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap
/-!
# Push-forward of fundamental classes (Fulton, Lemma 19.1.2)

Let `f : V → W` be a proper surjective morphism of complex varieties, `n = dim V`. Then
`f_* cl(V) = deg(V/W) cl(W)` in `H_{2n} W`, where `deg(V/W)` is the residue degree
`f.residueDegree (genericPoint V)`, the degree of `ℂ(V)` over `ℂ(W)`; if `dim W < dim V`,
`f_* cl(V) = 0` since `H_{2n} W = 0`.

## Main results

* `MMP.IsVarietyFundamentalClass.pushforward_eq_residueDegree_smul`: the case
  `dim W = dim V`.
* `MMP.IsVarietyFundamentalClass.pushforward_eq_zero_of_dimension_lt`: the case
  `dim W < dim V`.

## Implementation notes

By Lemma 19.1.1, `f_* cl(V) = r cl(W)` for a unique `r`. Over a connected open `U ⊆ W_reg(ℂ)`
with `f⁻¹(U) = U₁ ⊔ ⋯ ⊔ U_d`, each `U_i ⊆ V_reg(ℂ)` mapped biholomorphically onto `U`
(`GenericCovering.exists_preimage_eq_iUnion_diffeomorph`), restriction to `U` commutes with
push-forward and splits over the sheets (`restrict_pushforward_eq_sum_sheetMap`);
`cl(V)|_{U_i} = μ_{U_i}` and `cl(W)|_U = μ_U`, and `(f|_{U_i})_* μ_{U_i} = μ_U` (biholomorphic
maps preserve the complex orientation,
`diffeomorph_isOrientationPreserving_euclideanComplexOrientationBasis`). Hence
`r μ_U = d μ_U`, and `μ_U` freely generates `H_{2n} U` (`U` connected), so `r = d`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Lemma 19.1.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Manifold
open scoped ContDiff
open MMP.UnderlyingSpace MMP.FundamentalClass

namespace MMP

open MMP

variable {R : Type} [CommRing R] {V W : Scheme.{0}} [V.Over (Spec (.of ℂ))]
  [W.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsComplexScheme W] [IsIntegral V]
  [IsIntegral W] (f : V ⟶ W) [f.IsOver (Spec (.of ℂ))] [IsProper f]

/-- An open subset of `W(ℂ)` contained in `W_reg(ℂ)`, read in `W_reg(ℂ)`, is connected when it
is. -/
lemma connectedSpace_regularOpensInter {U : Opens (UnderlyingSpace ℂ W)}
    (hUc : IsConnected (U : Set (UnderlyingSpace ℂ W)))
    (hUreg : (U : Set (UnderlyingSpace ℂ W)) ⊆ regularPart ℂ W) :
    ConnectedSpace (regularOpensInter (𝕜 := ℂ) U) := by
  haveI := isConnected_iff_connectedSpace.1 hUc
  let e := borelMooreHomology.subOpensHomeo (Y := TopCat.of (UnderlyingSpace ℂ W))
    (regularOpens ℂ W) (U' := U) hUreg
  exact e.surjective.connectedSpace e.continuous

section Regular

variable (R) {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- An open subset `O ⊆ X_reg(ℂ)` of `X(ℂ)`, mapped homeomorphically onto the open subset
`regularOpensInter O` of `X_reg(ℂ)`. -/
abbrev regularOpensInterMap {O : Opens (UnderlyingSpace ℂ X)} (hO : O ≤ regularOpens ℂ X) :
    TopCat.of O ⟶ TopCat.of (regularOpensInter (𝕜 := ℂ) O) :=
  borelMooreHomology.subOpensMap (Y := TopCat.of (UnderlyingSpace ℂ X))
    (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X))) hO

/-- The map `regularOpensInterMap hO` is proper. -/
lemma isProperMap_regularOpensInterMap {O : Opens (UnderlyingSpace ℂ X)}
    (hO : O ≤ regularOpens ℂ X) : IsProperMap (regularOpensInterMap hO) :=
  borelMooreHomology.isProperMap_subOpensMap _ hO

/-- Restricting to `X_reg(ℂ)` and then to `O ∩ X_reg(ℂ)` is restricting to `O`, for an open
`O ⊆ X_reg(ℂ)`. -/
lemma restrict_regularOpensInter_restrict {O : Opens (UnderlyingSpace ℂ X)}
    (hO : O ≤ regularOpens ℂ X) (j : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) j) :
    borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ X))
        (regularOpensInter O) j
        (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X))
          (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X))) j a) =
      borelMooreHomology.pushforward R (ModuleCat.of R R) (regularOpensInterMap hO)
        (isProperMap_regularOpensInterMap hO) j
        (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X))
          O j a) :=
  borelMooreHomology.restrict_restrict_apply R (ModuleCat.of R R)
    (Y := TopCat.of (UnderlyingSpace ℂ X)) _ hO j a

end Regular

/-- **Lemma 19.1.2 of Fulton, equidimensional case**: for a proper surjective morphism
`f : V → W` of complex varieties of the same dimension `n`, `f_* cl(V) = deg(V/W) cl(W)` in
`H_{2n} W`. -/
theorem _root_.MMP.IsVarietyFundamentalClass.pushforward_eq_residueDegree_smul (hf : Function.Surjective f)
    {n : ℕ} {hn : (n : WithBot ℕ∞) = topologicalKrullDim V} (hnW : (n : WithBot ℕ∞) = topologicalKrullDim W)
    {cV : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ)}
    (hcV : IsVarietyFundamentalClass R hn cV)
    {cW : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ W)) (2 * n : ℕ)}
    (hcW : IsVarietyFundamentalClass R hnW cW) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
        (isProperMap_map (K := ℂ) f) (2 * n : ℕ) cV =
      (f.residueDegree (genericPoint V) : R) • cW := by
  classical
  have hF : IsProperMap (TopCat.ofHom (map (K := ℂ) f)) := isProperMap_map (K := ℂ) f
  have hdim : topologicalKrullDim V = topologicalKrullDim W := hn.symm.trans hnW
  obtain ⟨r, hr⟩ := hcW.bijective_smul.2
    (borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f)) hF
      (2 * n : ℕ) cV)
  simp only at hr
  obtain ⟨W₀, hW₀ne, -, -, hcov⟩ :=
    GenericCovering.exists_preimage_eq_iUnion_diffeomorph f hf hdim
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (W ↘ Spec (.of ℂ))
  obtain ⟨x₀, hx₀W₀, hx₀cl⟩ := nonempty_inter_closedPoints hW₀ne W₀.isOpen.isLocallyClosed
  obtain ⟨w, hw⟩ : ∃ p : UnderlyingSpace ℂ W, p.toHom (IsLocalRing.closedPoint ℂ) = x₀ :=
    ⟨(equivClosedPoints W).symm ⟨x₀, hx₀cl⟩, by
      rw [← equivClosedPoints_apply, Equiv.apply_symm_apply]⟩
  obtain ⟨U, hUc, hwU, -, hUreg, Ui, hdisj, hpre, hUireg, hrest⟩ := hcov w (hw ▸ hx₀W₀)
  obtain ⟨-, hφ⟩ := hrest n hnW
  have hpre' : (TopCat.ofHom (map (K := ℂ) f) : TopCat.of (UnderlyingSpace ℂ V) ⟶
      TopCat.of (UnderlyingSpace ℂ W)) ⁻¹' (U : Set (UnderlyingSpace ℂ W)) =
      ⋃ i, (Ui i : Set (UnderlyingSpace ℂ V)) := hpre
  choose φ hφ using hφ
  have hUle : U ≤ (regularOpens ℂ W : Opens (TopCat.of (UnderlyingSpace ℂ W))) := hUreg
  have hUile : ∀ i, Ui i ≤ (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) := hUireg
  haveI := connectedSpace_regularOpensInter hUc hUreg
  have hμU := hcW.isFundamentalClass_restrict U
  have hν := fun i ↦ hcV.isFundamentalClass_restrict (Ui i)
  have hor := fun i ↦ by
    letI := regularChartedSpace (𝕜 := ℂ) (X := W) hnW
    letI := regularChartedSpace (𝕜 := ℂ) (X := V) (hnW.trans hdim.symm)
    haveI := isManifold_regularOpens (𝕜 := ℂ) (X := W) hnW
    haveI := isManifold_regularOpens (𝕜 := ℂ) (X := V) (hnW.trans hdim.symm)
    haveI : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 1 (regularOpens ℂ W) :=
      IsManifold.of_le le_top
    haveI : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 1 (regularOpens ℂ V) :=
      IsManifold.of_le le_top
    exact MMP.diffeomorph_isOrientationPreserving_euclideanComplexOrientationBasis (φ i) le_top
  have hsheet := fun i ↦
    letI := regularChartedSpace (𝕜 := ℂ) (X := W) hnW
    letI := regularChartedSpace (𝕜 := ℂ) (X := V) hn
    hμU.eq_of_connectedSpace' ((hν i).pushforward_homeomorph R _ (hor i))
  have hkey : borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ W))
      (regularOpensInter U) ((2 * n : ℕ) : ℤ) (borelMooreHomology.restrict R (ModuleCat.of R R)
        (Y := TopCat.of (UnderlyingSpace ℂ W)) (regularOpens ℂ W : Opens (TopCat.of
        (UnderlyingSpace ℂ W))) ((2 * n : ℕ) : ℤ)
        (borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f)) hF
          ((2 * n : ℕ) : ℤ) cV)) = (f.residueDegree (genericPoint V) : R) • (borelMooreHomology.restrict R (ModuleCat.of R R)
          (Y := TopCat.of (regularOpens ℂ W)) (regularOpensInter U) ((2 * n : ℕ) : ℤ)
          (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ W))
          (regularOpens ℂ W : Opens (TopCat.of (UnderlyingSpace ℂ W))) ((2 * n : ℕ) : ℤ) cW)) := by
    rw [restrict_regularOpensInter_restrict R hUle,
      borelMooreHomology.restrict_pushforward_eq_sum_sheetMap R (ModuleCat.of R R)
        (TopCat.ofHom (map (K := ℂ) f)) hF U hdisj hpre', map_sum]
    have hterm : ∀ i, borelMooreHomology.pushforward R (ModuleCat.of R R)
        (regularOpensInterMap hUle) (isProperMap_regularOpensInterMap hUle) ((2 * n : ℕ) : ℤ)
        (borelMooreHomology.pushforward R (ModuleCat.of R R)
          (borelMooreHomology.sheetMap (TopCat.ofHom (map (K := ℂ) f)) U hpre' i)
          (borelMooreHomology.isProperMap_sheetMap (TopCat.ofHom (map (K := ℂ) f)) hF U hdisj
            hpre' i) ((2 * n : ℕ) : ℤ)
          (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
            (Ui i) ((2 * n : ℕ) : ℤ) cV)) = (borelMooreHomology.restrict R (ModuleCat.of R R)
              (Y := TopCat.of (regularOpens ℂ W)) (regularOpensInter U) ((2 * n : ℕ) : ℤ)
              (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of
              (UnderlyingSpace ℂ W)) (regularOpens ℂ W : Opens (TopCat.of (UnderlyingSpace ℂ W)))
              ((2 * n : ℕ) : ℤ) cW)) := by
      intro i
      rw [← hsheet i, restrict_regularOpensInter_restrict R (hUile i),
        borelMooreHomology.pushforward_pushforward_eq_comp,
        borelMooreHomology.pushforward_pushforward_eq_comp]
      refine borelMooreHomology.pushforward_apply_eq_of_hom_eq R (ModuleCat.of R R) ?_ _ _ _ _
      ext x : 1
      exact Subtype.ext (Subtype.ext (hφ i (regularOpensInterMap (hUile i) x)).symm)
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul R]
  rw [← hr, map_smul, map_smul] at hkey
  have hrd : r = f.residueDegree (genericPoint V) :=
    letI := regularChartedSpace (𝕜 := ℂ) (X := W) hnW
    (PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold
    (R := R) (Y := regularOpensInter (𝕜 := ℂ) U) (euclideanComplexOrientationBasis n)
      (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ W))
      (regularOpensInter U) ((2 * n : ℕ) : ℤ) (borelMooreHomology.restrict R (ModuleCat.of R R)
      (Y := TopCat.of (UnderlyingSpace ℂ W)) (regularOpens ℂ W : Opens (TopCat.of
      (UnderlyingSpace ℂ W))) ((2 * n : ℕ) : ℤ) cW))
      hμU).1 hkey
  rw [← hr, hrd]

/-- **Lemma 19.1.2 of Fulton, case `dim W < dim V`**: for a proper morphism `f : V → W` of complex
varieties with `dim W < n = dim V`, `f_* c = 0` for every `c ∈ H_{2n} V`, since `H_{2n} W = 0`. -/
theorem pushforward_eq_zero_of_dimension_lt {n : ℕ} (hn : (n : WithBot ℕ∞) = topologicalKrullDim V)
    (hlt : topologicalKrullDim W < topologicalKrullDim V)
    (c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ)) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
        (isProperMap_map (K := ℂ) f) (2 * n : ℕ) c = 0 := by
  haveI : Nonempty (IrreducibleCloseds W) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim W := Order.krullDim_nonneg
  rw [← hn] at hlt
  have hle : topologicalKrullDim W ≤ ((n - 1 : ℕ) : WithBot ℕ∞) ∧ 1 ≤ n := by
    generalize topologicalKrullDim W = x at hlt h0
    induction x with
    | bot => exact absurd h0 (by simp)
    | coe y =>
      induction y with
      | top => exact absurd hlt (by simp)
      | coe y =>
        have h1 : y < n := by exact_mod_cast hlt
        refine ⟨?_, by omega⟩
        have h2 : (y : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := Nat.cast_le.2 (by omega)
        exact WithBot.coe_le_coe.2 h2
  have hz := IsComplexScheme.isZero_borelMooreHomology_of_dimension_le (X := W) R hle.1
    (i := ((2 * n : ℕ) : ℤ)) (by push_cast; omega)
  exact (ModuleCat.isZero_iff_subsingleton.1 hz).elim _ _

end MMP
