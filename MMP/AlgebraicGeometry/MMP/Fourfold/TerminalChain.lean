module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction

/-!
# Decreased boundaries, terminal bridges and terminal chains of fourfolds

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt tail of fourfolds, with stable
low-discrepancy set `I_∞`, and let `(p_i, Θ_i)`, `p_i : Y_i ⟶ X_i`, be a crepant junction of
`(X_i, B_i)` extracting `I_∞`, with divisors `E_{i,s}`, `s ∈ I_∞`, on `Y_i`. The *decreased
boundary* is `Θ_i' = (p_i)⁻¹_* B_i + ∑_{s ∈ I_∞} (1 - a_{i+1}(s)) E_{i,s}`.

A *terminal bridge* from `(p_i, Θ_i)` to a crepant junction `(p_{i+1}, Θ_{i+1})` of
`(X_{i+1}, B_{i+1})` extracting `I_∞` is a finite relative program over `Z_i` (via `f_i ∘ p_i`)
from `(Y_i, Θ_i')` in which every `g_k` is small, whose end is `(Y_{i+1}, Θ_{i+1})`, and whose
composite birational map `φ : Y_i ⤏ Y_{i+1}` satisfies `p_{i+1} ∘ φ = (f_i⁺)⁻¹ ∘ f_i ∘ p_i`. Its
moves are the coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` followed by the flips.

A *terminal chain* over the tail is a sequence of crepant junctions `(p_i, Θ_i)_{i ≥ 0}` of
`(X_i, B_i)` extracting `I_∞` together with a terminal bridge from each to the next. Its models
are, in order, `(Y_0, Θ_0)`, `(Y_0, Θ_0')`, the successive models of the first bridge ending with
`(Y_1, Θ_1)`, then `(Y_1, Θ_1')`, and so on; consecutive models are related by a coefficient
decrease or by a flip.

## Main definitions

* `MMP.Fourfold.IsCoefficientDecrease`, `MMP.Fourfold.IsFlipMove`: the two kinds of moves
  between pairs.
* `MMP.Fourfold.StabilizedSmallKltTail.stableLowDiscrepancySetAt`: the image of `I_∞` in the
  valuations of `k(X_i)`.
* `MMP.Fourfold.StabilizedSmallKltTail.IsDecreasedBoundary`: the decreased boundary `Θ_i'`.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge`: terminal bridges.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain`: terminal chains.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.model`,
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.modelBoundary`,
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.modelIndexSeq`: the models of a terminal
  chain, and their enumeration in order.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge.isCoefficientDecrease`,
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge.isFlipMove`: the moves of a bridge.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isCoefficientDecrease_or_isFlipMove`:
  consecutive models of a terminal chain are related by a coefficient decrease or by a flip.

## Implementation notes

* `I_∞` is a set of valuations of `k(X_0)`; it is transported to the valuations of `k(X_i)` by
  `MMP.Fourfold.StepSequence.Corresponds`. A junction of `(X_i, B_i)` *extracting `I_∞`* is a
  crepant junction extracting a finite set `I` of valuations of `k(X_i)` equal to this image.
* For a valuation `s` of `k(X_i)`, `a_{i+1}(s)` is the log discrepancy over `(X_{i+1}, B_{i+1})`
  of the valuation `s'` of `k(X_{i+1})` corresponding to `s` under `k(X_i) ≅ k(Z_i) ≅ k(X_{i+1})`
  (`MMP.Fourfold.StepSequence.IsTransportedValuation`). Log discrepancies enter through the
  predicate `MMP.Fourfold.IsValuationLogDiscrepancy`, so the decreased boundary is a predicate
  on a divisor of `Y_i`. It is defined for a junction extracting any finite set `I`; the source
  takes `I` the image of `I_∞`.
* The program of a bridge is run with a canonical divisor `K` of `Y_i`, carried as data. Its end
  `(Y_{i+1}, Θ_{i+1})` is an isomorphism `e : V_m ≅ Y_{i+1}` over `ℂ` with `Θ_m = e⁻¹_* Θ_{i+1}`.
  The composite birational map is `φ = e ∘ ψ`, `ψ : Y_i ⤏ V_m` the composite map of the program
  (`MMP.Fourfold.RelativeFourfoldProgram.compositeMap`), and `p_{i+1} ∘ φ = (f_i⁺)⁻¹ ∘ f_i ∘ p_i`
  is stated as `f_i⁺ ∘ p_{i+1} ∘ φ = f_i ∘ p_i`, equivalent since `f_i⁺` is birational. That
  `e` is compatible with the maps to `Z_i` (`π_m = f_i⁺ ∘ p_{i+1} ∘ e`) follows
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge.toBase_end_eq`).
* A *coefficient decrease* `(Y, Θ) ⇝ (Y', Θ')` is an isomorphism `Y ≅ Y'` over `ℂ`, only the
  boundary changing (that `Θ_i' ≤ Θ_i` is the source's lemma `a_i(s) ≤ a_{i+1}(s)`); a *flip*
  `(Y, Θ) ⇝ (Y', Θ')` is a step diagram
  `(Y, Θ) → T ← (Y', Θ')` in which both morphisms are small.
* The models of a terminal chain are indexed by pairs `(i, none)`, the junction `(Y_i, Θ_i)`,
  and `(i, some k)`, `k < m_i`, the model `(V_k, Θ_k)` of the `i`-th bridge, `(i, some 0)` being
  the decreased pair `(Y_i, Θ_i')`; the end `V_{m_i}` of the `i`-th bridge is the junction
  `(Y_{i+1}, Θ_{i+1})`, so it is not listed again. When `m_i = 0` the decreased pair is the end
  of the bridge, identified with `(Y_{i+1}, Θ_{i+1})`. The order is given by
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.next`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Inverse transforms under isomorphisms -/

section InverseTransformIso

universe u

variable {X Y W : Scheme.{u}}

/-- The biregular locus of an isomorphism is everything. -/
private theorem biregularLocus_eq_top_of_isIso (g : Y ⟶ X) [IsIso g] : biregularLocus g = ⊤ :=
  top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff g).mpr inferInstance))

/-- Under an isomorphism `g`, the inverse transform of a closed subset is its preimage. -/
private theorem coe_inverseTransform_of_isIso (g : Y ⟶ X) [IsIso g] (Z : Closeds X) :
    (inverseTransform g Z : Set Y) = g ⁻¹' (Z : Set X) := by
  rw [inverseTransform, biregularLocus_eq_top_of_isIso, Closeds.coe_closure]
  simp only [Opens.coe_top, Set.inter_univ]
  exact (Z.isClosed.preimage g.continuous).closure_eq

/-- Under an isomorphism `g`, `g⁻¹_* D = E` exactly when `E` is supported on `g⁻¹(D)`. -/
private theorem inverseTransformPrimeDivisor_eq_some_iff_of_isIso (g : Y ⟶ X) [IsIso g]
    (D : MMP.Mori.PrimeDivisor X) (E : MMP.Mori.PrimeDivisor Y) :
    inverseTransformPrimeDivisor g D = some E ↔ E.support = g ⁻¹' D.support := by
  rw [inverseTransformPrimeDivisor_eq_some_iff, biregularLocus_eq_top_of_isIso]
  have hne : (D.support ∩ ((⊤ : X.Opens) : Set X)).Nonempty := by
    have := D.integral
    obtain ⟨x⟩ : Nonempty D.idealSheaf.subscheme := inferInstance
    refine ⟨D.idealSheaf.subschemeι x, ?_, trivial⟩
    rw [AlgebraicGeometry.PrimeDivisor.support, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨x, rfl⟩
  simp only [hne, true_and]
  rw [inverseTransformIdeal]
  constructor
  · intro h
    have := congrArg (fun I ↦ (I.support : Set Y)) h
    simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    rw [AlgebraicGeometry.PrimeDivisor.support, this, coe_inverseTransform_of_isIso]
  · intro h
    have := E.integral
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf _ rfl]
    congr 1
    ext1
    rwa [coe_inverseTransform_of_isIso]

/-- Under an isomorphism `g`, every prime divisor has a transform. -/
private theorem exists_inverseTransformPrimeDivisor_of_isIso (g : Y ⟶ X) [IsIso g]
    (D : MMP.Mori.PrimeDivisor X) : ∃ E, inverseTransformPrimeDivisor g D = some E := by
  have hco : Order.coheight (inv g D.genericPoint) = 1 := by
    rw [coheight_eq_of_isOpenImmersion (inv g)]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint D
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (inverseTransformPrimeDivisor_eq_some_iff_of_isIso g D _).mpr ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have hh := (Scheme.homeoOfIso (asIso g)).preimage_closure {D.genericPoint}
  have hs : (Scheme.homeoOfIso (asIso g)) ⁻¹' {D.genericPoint} = {inv g D.genericPoint} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    change g y = _ ↔ _
    constructor
    · intro h
      rw [← h, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl
    · intro h
      rw [h, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
  rw [hs] at hh
  exact hh.symm

/-- The inverse transform under the identity is the identity: `(𝟙_Y)⁻¹_* D = D`. -/
theorem inverseTransformDivisor_id {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Y) :
    inverseTransformDivisor (𝟙 Y) D = D := by
  have : inverseTransformDivisor (R := R) (𝟙 Y) = AddMonoidHom.id _ := by
    refine Finsupp.addHom_ext fun P r ↦ ?_
    rw [AddMonoidHom.id_apply]
    exact inverseTransformDivisor_single_of_eq_some
      ((inverseTransformPrimeDivisor_eq_some_iff_of_isIso _ P P).mpr rfl) r
  exact DFunLike.congr_fun this D

/-- Inverse transforms under isomorphisms compose: `(a ≫ b)⁻¹_* D = a⁻¹_* (b⁻¹_* D)`. -/
theorem inverseTransformDivisor_comp_of_isIso {R : Type*} [AddCommMonoid R] (a : W ⟶ Y)
    (b : Y ⟶ X) [IsIso a] [IsIso b] (D : DivisorWithCoeffs R X) :
    inverseTransformDivisor (a ≫ b) D =
      inverseTransformDivisor a (inverseTransformDivisor b D) := by
  have : inverseTransformDivisor (R := R) (a ≫ b) =
      (inverseTransformDivisor a).comp (inverseTransformDivisor b) := by
    refine Finsupp.addHom_ext fun P r ↦ ?_
    obtain ⟨E, hE⟩ := exists_inverseTransformPrimeDivisor_of_isIso b P
    obtain ⟨F, hF⟩ := exists_inverseTransformPrimeDivisor_of_isIso a E
    have hF' : inverseTransformPrimeDivisor (a ≫ b) P = some F := by
      rw [inverseTransformPrimeDivisor_eq_some_iff_of_isIso] at hE hF ⊢
      rw [hF, hE]
      rfl
    rw [AddMonoidHom.comp_apply, inverseTransformDivisor_single_of_eq_some hE,
      inverseTransformDivisor_single_of_eq_some hF, inverseTransformDivisor_single_of_eq_some hF']
  exact DFunLike.congr_fun this D

end InverseTransformIso

/-! ### Moves between pairs -/

section Moves

variable {Y Y' : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsIntegral Y'] [CompactSpace Y'] [IsLocallyNoetherian Y'] [IsNormal Y']

/-- `(Y, Θ) ⇝ (Y', Θ')` is a *coefficient-decrease move*: the pairs live on the same variety,
that is, there is an isomorphism `e : Y ≅ Y'` over `ℂ`, and only the boundary is changed. In a
terminal bridge this is the move `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')`; that its coefficients do decrease,
`Θ_i' ≤ Θ_i`, amounts to `a_i(s) ≤ a_{i+1}(s)`, a separate lemma of the source
(`lem_oai4_graph`), and is not part of the definition of the move. -/
@[mmp "def_oai4_terminal_bridge"]
def IsCoefficientDecrease (sY : Y ⟶ Spec (.of ℂ)) (_Θ : QDivisor Y) (sY' : Y' ⟶ Spec (.of ℂ))
    (_Θ' : QDivisor Y') : Prop :=
  ∃ e : Y ≅ Y', e.hom ≫ sY' = sY

/-- `(Y, Θ) ⇝ (Y', Θ')` is a *flip*: a step diagram `(Y, Θ) → T ← (Y₀, Θ₀)` by `g`, `g⁺`
(`MMP.Fourfold.IsFourfoldStepDiagram`, for some canonical divisor `K` of `Y`) in which `g` is
small (`g⁺` is small by definition), `Θ₀ = (g⁺)⁻¹_* g_* Θ`, and `(Y', Θ')` is `(Y₀, Θ₀)` up to an
isomorphism `e : Y₀ ≅ Y'` over `ℂ` (`Θ₀ = e⁻¹_* Θ'`): a flip is determined up to isomorphism. -/
@[mmp "def_oai4_terminal_bridge"]
def IsFlipMove (sY : Y ⟶ Spec (.of ℂ)) (Θ : QDivisor Y) (sY' : Y' ⟶ Spec (.of ℂ))
    (Θ' : QDivisor Y') : Prop :=
  ∃ (Y₀ : Scheme.{0}) (_ : IsIntegral Y₀) (_ : CompactSpace Y₀) (_ : IsLocallyNoetherian Y₀)
    (_ : IsNormal Y₀) (sY₀ : Y₀ ⟶ Spec (.of ℂ)) (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℂ))
    (K : Divisor Y) (g : Y ⟶ T) (gp : Y₀ ⟶ T) (e : Y₀ ≅ Y'),
    IsFourfoldStepDiagram sY sT sY₀ K Θ g gp ∧ IsSmallMorphism sY sT g ∧
      e.hom ≫ sY' = sY₀ ∧ flipTransform g gp Θ = inverseTransformDivisor e.hom Θ'

omit [IsIntegral Y] [IsIntegral Y'] [CompactSpace Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] in
/-- A flip `(Y, Θ) ⇝ (Y', Θ')` is a flip `(Y, Θ) ⇝ (Y'', Θ'')` for any isomorphism `Y' ≅ Y''`
over `ℂ` carrying `Θ''` to `Θ'`. -/
theorem IsFlipMove.of_iso {Y'' : Scheme.{0}} [IsIntegral Y''] [CompactSpace Y'']
    [IsLocallyNoetherian Y''] [IsNormal Y''] {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y}
    {sY' : Y' ⟶ Spec (.of ℂ)} {Θ' : QDivisor Y'} {sY'' : Y'' ⟶ Spec (.of ℂ)}
    {Θ'' : QDivisor Y''} (h : IsFlipMove sY Θ sY' Θ') (e : Y' ≅ Y'') (he : e.hom ≫ sY'' = sY')
    (hΘ : Θ' = inverseTransformDivisor e.hom Θ'') : IsFlipMove sY Θ sY'' Θ'' := by
  obtain ⟨Y₀, i₁, i₂, i₃, i₄, sY₀, T, sT, K, g, gp, e₀, hd, hs, he₀, hΘ₀⟩ := h
  refine ⟨Y₀, i₁, i₂, i₃, i₄, sY₀, T, sT, K, g, gp, e₀ ≪≫ e, hd, hs, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, he, he₀]
  · rw [hΘ₀, hΘ, Iso.trans_hom, inverseTransformDivisor_comp_of_isIso]

end Moves

namespace StabilizedSmallKltTail

variable {T : StabilizedSmallKltTail}

variable (T) in
/-- The image of the stable low-discrepancy set `I_∞` in the valuations of `k(X_i)`: the
valuations of `k(X_i)` corresponding (`MMP.Fourfold.StepSequence.Corresponds`) to an element of
`I_∞`. A crepant junction of `(X_i, B_i)` *extracts `I_∞`* if it extracts this set. -/
def stableLowDiscrepancySetAt (i : ℕ) :
    Set (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))) :=
  {η | ∃ ξ ∈ T.stableLowDiscrepancySet, T.Corresponds i ξ η}

@[simp]
theorem mem_stableLowDiscrepancySetAt {i : ℕ}
    {η : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))} :
    η ∈ T.stableLowDiscrepancySetAt i ↔ ∃ ξ ∈ T.stableLowDiscrepancySet, T.Corresponds i ξ η :=
  Iff.rfl

/-! ### Decreased boundaries -/

/-- `Θ'` is the *decreased boundary* of a crepant junction `(p_i, Θ_i)` of `(X_i, B_i)`
extracting `I`, `p_i : Y_i ⟶ X_i`, with divisors `E_{i,s}` (`s ∈ I`):
`Θ' = (p_i)⁻¹_* B_i + ∑_{s ∈ I} (1 - a_{i+1}(s)) E_{i,s}`, where `a_{i+1}(s)` is the log
discrepancy `a(s'; X_{i+1}, B_{i+1})` of the valuation `s'` of `k(X_{i+1})` corresponding to `s`
(`MMP.Fourfold.StepSequence.IsTransportedValuation`). In the source `I` is (the image in `k(X_i)`
of) `I_∞`. -/
@[mmp "def_oai4_decreased_boundary"]
def IsDecreasedBoundary {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction (T.sX i) (T.B i) I) (Θ' : QDivisor J.Y) : Prop :=
  ∃ a : I → ℚ,
    (∀ s : I, ∃ s' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)),
      T.IsTransportedValuation i s s' ∧ T.IsLogDiscrepancyAt (i + 1) s' (a s)) ∧
    Θ' = inverseTransformDivisor J.p (T.B i) + ∑ s : I, Finsupp.single (J.E s) (1 - a s)

/-! ### Terminal bridges -/

/-- A *terminal bridge* from a crepant junction `(p_i, Θ_i)` of `(X_i, B_i)`,
`p_i : Y_i ⟶ X_i`, to a crepant junction `(p_{i+1}, Θ_{i+1})` of `(X_{i+1}, B_{i+1})`,
`p_{i+1} : Y_{i+1} ⟶ X_{i+1}`, both extracting `I_∞`: a canonical divisor `K` of `Y_i`, the
decreased boundary `Θ_i'` of `(p_i, Θ_i)`, and a finite relative program
`(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `k < m`, over `Z_i` via `f_i ∘ p_i` from `(Y_i, Θ_i')`
(`MMP.Fourfold.RelativeFourfoldProgram`), such that

* every `g_k`, `k < m`, is small;
* its end is `(Y_{i+1}, Θ_{i+1})`: there is an isomorphism `e : V_m ≅ Y_{i+1}` over `ℂ` with
  `Θ_m = e⁻¹_* Θ_{i+1}`;
* its composite birational map `φ = e ∘ ψ : Y_i ⤏ Y_{i+1}`, `ψ : Y_i ⤏ V_m` the composite of the
  steps, satisfies `p_{i+1} ∘ φ = (f_i⁺)⁻¹ ∘ f_i ∘ p_i`, that is, `f_i⁺ ∘ p_{i+1} ∘ φ = f_i ∘ p_i`
  as rational maps.

The *moves* of the bridge are the coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')`
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge.isCoefficientDecrease`) followed by the flips
`(V_k, Θ_k) ⇝ (V_{k+1}, Θ_{k+1})`
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge.isFlipMove`). -/
@[mmp "def_oai4_terminal_bridge"]
structure TerminalBridge (i : ℕ)
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction (T.sX i) (T.B i) I)
    (J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I') where
  /-- The source junction extracts `I_∞`. -/
  coe_source : (I : Set _) = T.stableLowDiscrepancySetAt i
  /-- The target junction extracts `I_∞`. -/
  coe_target : (I' : Set _) = T.stableLowDiscrepancySetAt (i + 1)
  /-- The canonical divisor of `Y_i` with which the program is run. -/
  K : Divisor J.Y
  /-- The decreased boundary `Θ_i'` on `Y_i`. -/
  Θ' : QDivisor J.Y
  /-- `Θ'` is the decreased boundary of `J`. -/
  isDecreasedBoundary : IsDecreasedBoundary J Θ'
  /-- The finite relative program over `Z_i` from `(Y_i, Θ_i')`. -/
  P : RelativeFourfoldProgram J.sY (T.sZ i) (J.p ≫ T.f i) K Θ'
  /-- Every flipping contraction `g_k` is small. -/
  isSmallMorphism : ∀ k < P.m, IsSmallMorphism (P.modelStructure k) (P.sT k) (P.g k)
  /-- The identification `e : V_m ≅ Y_{i+1}` of the end of the program. -/
  e : P.endModel ≅ J'.Y
  /-- `e` is an isomorphism over `ℂ`. -/
  comp_sY : e.hom ≫ J'.sY = P.modelStructure P.m
  /-- `Θ_m = e⁻¹_* Θ_{i+1}`. -/
  endBoundary_eq : P.endBoundary = inverseTransformDivisor e.hom J'.Θ
  /-- `f_i⁺ ∘ p_{i+1} ∘ e ∘ ψ = f_i ∘ p_i`. -/
  compHom_eq : ((P.compositeMap.compHom e.hom).compHom J'.p).compHom (T.fp i) =
    (J.p ≫ T.f i).toRationalMap

namespace TerminalBridge

variable {i : ℕ} {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
  {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
  {J : FourfoldCrepantJunction (T.sX i) (T.B i) I}
  {J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'}
  (β : TerminalBridge i J J')

/-- The composite birational map `φ : Y_i ⤏ Y_{i+1}` of a terminal bridge. -/
@[mmp "def_oai4_terminal_bridge"]
def compositeMap : RationalMap J.Y J'.Y := β.P.compositeMap.compHom β.e.hom

/-- `p_{i+1} ∘ φ = (f_i⁺)⁻¹ ∘ f_i ∘ p_i`, in the form `f_i⁺ ∘ p_{i+1} ∘ φ = f_i ∘ p_i`. -/
theorem compHom_compositeMap :
    (β.compositeMap.compHom J'.p).compHom (T.fp i) = (J.p ≫ T.f i).toRationalMap :=
  β.compHom_eq

/-- The end of a terminal bridge is `(Y_{i+1}, Θ_{i+1})` as a model over `Z_i`:
`π_m = f_i⁺ ∘ p_{i+1} ∘ e`. -/
theorem toBase_end_eq : β.P.toBase β.P.m = β.e.hom ≫ J'.p ≫ T.fp i := by
  have : IsSeparated (T.sZ i) := β.P.isProjectiveVariety_base.1.toIsSeparated
  have hsep : IsSeparated (T.Z i ↘ ⊤_ Scheme) := by
    have : (T.Z i ↘ ⊤_ Scheme) = T.sZ i ≫ Limits.terminal.from (Spec (.of ℂ)) :=
      Subsingleton.elim _ _
    rw [this]
    infer_instance
  have H := β.P.isOver_compositePartialIso β.P.m le_rfl
  set ψ := β.P.compositePartialIso β.P.m le_rfl with hψ
  have h2 := β.compHom_eq
  rw [RelativeFourfoldProgram.compositeMap, ← hψ, Scheme.PartialIso.toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at h2
  have h4 : ψ.iso.hom ≫ ψ.target.ι ≫ β.P.toBase β.P.m =
      ψ.iso.hom ≫ ψ.target.ι ≫ β.e.hom ≫ J'.p ≫ T.fp i := by
    rw [H]
    exact ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp h2).symm
  have : IsDominant ψ.target.ι := Opens.isDominant_ι ψ.dense_target
  exact ext_of_isDominant_of_isSeparated (T.Z i ↘ ⊤_ Scheme) (Subsingleton.elim _ _)
    ψ.target.ι ((cancel_epi ψ.iso.hom).mp h4)

/-- The first move of a terminal bridge is the coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')`. -/
@[mmp "def_oai4_terminal_bridge"]
theorem isCoefficientDecrease : IsCoefficientDecrease J.sY J.Θ J.sY β.Θ' :=
  ⟨Iso.refl _, Category.id_comp _⟩

/-- The further moves of a terminal bridge are the flips `(V_k, Θ_k) ⇝ (V_{k+1}, Θ_{k+1})`,
`k < m`. -/
@[mmp "def_oai4_terminal_bridge"]
theorem isFlipMove {k : ℕ} (hk : k < β.P.m) :
    IsFlipMove (β.P.modelStructure k) (β.P.boundary k) (β.P.modelStructure (k + 1))
      (β.P.boundary (k + 1)) :=
  ⟨β.P.model (k + 1), inferInstance, inferInstance, inferInstance, inferInstance,
    β.P.modelStructure (k + 1), β.P.T k, β.P.sT k, β.P.canonical k, β.P.g k, β.P.gp k,
    Iso.refl _, β.P.isFourfoldStepDiagram k hk, β.isSmallMorphism k hk, Category.id_comp _,
    (β.P.boundary_succ_eq_flipTransform hk).symm.trans (inverseTransformDivisor_id _).symm⟩

end TerminalBridge

/-! ### Terminal chains -/

variable (T) in
/-- A *terminal chain* over a stabilized small klt tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`: a
sequence `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, of crepant junctions of `(X_i, B_i)` extracting
`I_∞` (that is, extracting finite sets `I_i` equal to the image of `I_∞` in the valuations of
`k(X_i)`, recorded by the bridges), together with, for each `i`, a terminal bridge from
`(p_i, Θ_i)` to `(p_{i+1}, Θ_{i+1})`.

Its *models* (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.model`, listed in order by
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.modelIndexSeq`) are, in order, `(Y_0, Θ_0)`,
`(Y_0, Θ_0')`, the successive models of the first bridge ending with `(Y_1, Θ_1)`, then
`(Y_1, Θ_1')`, and so on; consecutive models are related by a coefficient decrease or by a flip
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isCoefficientDecrease_or_isFlipMove`). -/
@[mmp "def_oai4_terminal_chain"]
structure TerminalChain where
  /-- The finite set `I_i` (the image of `I_∞`) extracted by the `i`-th junction. -/
  I : ∀ i, Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))
  /-- The crepant junction `(p_i, Θ_i)` of `(X_i, B_i)`. -/
  junction : ∀ i, FourfoldCrepantJunction (T.sX i) (T.B i) (I i)
  /-- The terminal bridge from the `i`-th junction to the next. -/
  bridge : ∀ i, TerminalBridge i (junction i) (junction (i + 1))

namespace TerminalChain

variable (C : TerminalChain T)

/-- Every junction of a terminal chain extracts `I_∞`. -/
theorem coe_I (i : ℕ) : (C.I i : Set _) = T.stableLowDiscrepancySetAt i :=
  (C.bridge i).coe_source

/-- The indices of the models of a terminal chain: `(i, none)` is the junction `(Y_i, Θ_i)` and
`(i, some k)`, `k < m_i`, is the model `(V_k, Θ_k)` of the `i`-th bridge, `(i, some 0)` being the
decreased pair `(Y_i, Θ_i')`. -/
@[mmp "def_oai4_terminal_chain"]
abbrev ModelIndex : Type := Σ i : ℕ, Option (Fin (C.bridge i).P.m)

/-- The variety of a model of a terminal chain. -/
@[mmp "def_oai4_terminal_chain"]
def model : C.ModelIndex → Scheme.{0}
  | ⟨i, none⟩ => (C.junction i).Y
  | ⟨i, some k⟩ => (C.bridge i).P.model k

/-- The structure morphism to `Spec ℂ` of a model of a terminal chain. -/
def modelStructure : ∀ x : C.ModelIndex, C.model x ⟶ Spec (.of ℂ)
  | ⟨i, none⟩ => (C.junction i).sY
  | ⟨i, some k⟩ => (C.bridge i).P.modelStructure k

/-- The boundary of a model of a terminal chain. -/
@[mmp "def_oai4_terminal_chain"]
def modelBoundary : ∀ x : C.ModelIndex, QDivisor (C.model x)
  | ⟨i, none⟩ => (C.junction i).Θ
  | ⟨i, some k⟩ => (C.bridge i).P.boundary k

/-- Every model of a terminal chain is integral. -/
instance isIntegral_model (x : C.ModelIndex) : IsIntegral (C.model x) := by
  rcases x with ⟨i, _ | k⟩ <;> dsimp only [model] <;> infer_instance

/-- Every model of a terminal chain is quasi-compact. -/
instance compactSpace_model (x : C.ModelIndex) : CompactSpace (C.model x) := by
  rcases x with ⟨i, _ | k⟩
  · exact (C.junction i).compactSpace
  · have := (C.junction i).compactSpace
    exact modelSeq.compactSpace (X := (C.junction i).Y) _

/-- Every model of a terminal chain is locally Noetherian. -/
instance isLocallyNoetherian_model (x : C.ModelIndex) : IsLocallyNoetherian (C.model x) := by
  rcases x with ⟨i, _ | k⟩ <;> dsimp only [model] <;> infer_instance

/-- Every model of a terminal chain is normal. -/
instance isNormal_model (x : C.ModelIndex) : IsNormal (C.model x) := by
  rcases x with ⟨i, _ | k⟩ <;> dsimp only [model] <;> infer_instance

/-- The model following a model of a terminal chain: after the junction `(Y_i, Θ_i)` comes the
decreased pair `(Y_i, Θ_i') = (V_0, Θ_0)` of the `i`-th bridge, after `(V_k, Θ_k)` comes
`(V_{k+1}, Θ_{k+1})`, and the end `(V_{m_i}, Θ_{m_i})` is the junction `(Y_{i+1}, Θ_{i+1})`. -/
def next : C.ModelIndex → C.ModelIndex
  | ⟨i, none⟩ => if h : 0 < (C.bridge i).P.m then ⟨i, some ⟨0, h⟩⟩ else ⟨i + 1, none⟩
  | ⟨i, some k⟩ =>
    if h : k.1 + 1 < (C.bridge i).P.m then ⟨i, some ⟨k.1 + 1, h⟩⟩ else ⟨i + 1, none⟩

/-- When the `i`-th bridge has a step, the junction `(Y_i, Θ_i)` is followed by the decreased
pair `(V_0, Θ_0)`. -/
theorem next_none_of_pos {i : ℕ} (h : 0 < (C.bridge i).P.m) :
    C.next ⟨i, none⟩ = ⟨i, some ⟨0, h⟩⟩ := by
  simp only [next, h, ↓reduceDIte]

/-- When the `i`-th bridge has no step, the junction `(Y_i, Θ_i)` is followed by the next
junction `(Y_{i+1}, Θ_{i+1})`. -/
theorem next_none_of_not_pos {i : ℕ} (h : ¬0 < (C.bridge i).P.m) :
    C.next ⟨i, none⟩ = ⟨i + 1, none⟩ := by
  simp only [next, h, ↓reduceDIte]

/-- A model `(V_k, Θ_k)` of the `i`-th bridge with `k + 1 < m_i` is followed by
`(V_{k+1}, Θ_{k+1})`. -/
theorem next_some_of_lt {i : ℕ} {k : Fin (C.bridge i).P.m} (h : k.1 + 1 < (C.bridge i).P.m) :
    C.next ⟨i, some k⟩ = ⟨i, some ⟨k.1 + 1, h⟩⟩ := by
  simp only [next, h, ↓reduceDIte]

/-- The last listed model `(V_k, Θ_k)` of the `i`-th bridge is followed by the next junction
`(Y_{i+1}, Θ_{i+1})`. -/
theorem next_some_of_not_lt {i : ℕ} {k : Fin (C.bridge i).P.m}
    (h : ¬k.1 + 1 < (C.bridge i).P.m) : C.next ⟨i, some k⟩ = ⟨i + 1, none⟩ := by
  simp only [next, h, ↓reduceDIte]

/-- The models of a terminal chain in order: the `n`-th model, starting from the junction
`(Y_0, Θ_0)`. -/
@[mmp "def_oai4_terminal_chain"]
def modelIndexSeq (n : ℕ) : C.ModelIndex := C.next^[n] ⟨0, none⟩

/-- The first model of a terminal chain is the junction `(Y_0, Θ_0)`. -/
@[simp]
theorem modelIndexSeq_zero : C.modelIndexSeq 0 = ⟨0, none⟩ :=
  rfl

/-- The `(n + 1)`-th model of a terminal chain follows the `n`-th one. -/
theorem modelIndexSeq_succ (n : ℕ) : C.modelIndexSeq (n + 1) = C.next (C.modelIndexSeq n) :=
  Function.iterate_succ_apply' _ _ _

/-- The boundary of the decreased pair `(Y_i, Θ_i')`, the model following the junction
`(Y_i, Θ_i)` when the `i`-th bridge has a step, is the decreased boundary of the `i`-th
junction. -/
theorem isDecreasedBoundary_modelBoundary (i : ℕ) (h : 0 < (C.bridge i).P.m) :
    IsDecreasedBoundary (C.junction i) (C.modelBoundary ⟨i, some ⟨0, h⟩⟩) :=
  (C.bridge i).isDecreasedBoundary

/-- Consecutive models of a terminal chain are related by a coefficient decrease or by a flip. -/
@[mmp "def_oai4_terminal_chain"]
theorem isCoefficientDecrease_or_isFlipMove (n : ℕ) :
    IsCoefficientDecrease (C.modelStructure (C.modelIndexSeq n))
        (C.modelBoundary (C.modelIndexSeq n)) (C.modelStructure (C.modelIndexSeq (n + 1)))
        (C.modelBoundary (C.modelIndexSeq (n + 1))) ∨
      IsFlipMove (C.modelStructure (C.modelIndexSeq n)) (C.modelBoundary (C.modelIndexSeq n))
        (C.modelStructure (C.modelIndexSeq (n + 1)))
        (C.modelBoundary (C.modelIndexSeq (n + 1))) := by
  rw [modelIndexSeq_succ]
  generalize C.modelIndexSeq n = x
  rcases x with ⟨i, _ | k⟩
  · by_cases h : 0 < (C.bridge i).P.m
    · rw [C.next_none_of_pos h]
      exact Or.inl ⟨Iso.refl _, Category.id_comp _⟩
    · rw [C.next_none_of_not_pos h]
      left
      have key : ∀ (m : ℕ) (e : (C.bridge i).P.model m ≅ (C.junction (i + 1)).Y),
          e.hom ≫ (C.junction (i + 1)).sY = (C.bridge i).P.modelStructure m → m = 0 →
          IsCoefficientDecrease (C.junction i).sY (C.junction i).Θ (C.junction (i + 1)).sY
            (C.junction (i + 1)).Θ := by
        rintro m e he rfl
        exact ⟨e, he⟩
      exact key _ (C.bridge i).e (C.bridge i).comp_sY (by omega)
  · by_cases h : k.1 + 1 < (C.bridge i).P.m
    · rw [C.next_some_of_lt h]
      exact Or.inr ((C.bridge i).isFlipMove k.2)
    · rw [C.next_some_of_not_lt h]
      right
      have key : ∀ (m : ℕ) (e : (C.bridge i).P.model m ≅ (C.junction (i + 1)).Y),
          e.hom ≫ (C.junction (i + 1)).sY = (C.bridge i).P.modelStructure m →
          (C.bridge i).P.boundary m = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ →
          m = k.1 + 1 →
          IsFlipMove ((C.bridge i).P.modelStructure k) ((C.bridge i).P.boundary k)
            (C.junction (i + 1)).sY (C.junction (i + 1)).Θ := by
        rintro m e he hΘ rfl
        exact ((C.bridge i).isFlipMove k.2).of_iso e he hΘ
      exact key _ (C.bridge i).e (C.bridge i).comp_sY (C.bridge i).endBoundary_eq
        (by have := k.2; omega)

end TerminalChain

end StabilizedSmallKltTail

end MMP.Fourfold
