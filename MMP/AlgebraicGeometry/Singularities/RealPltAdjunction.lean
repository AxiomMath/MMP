module

public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.EffectiveResidueAdjunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
public import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
public import MMP.AlgebraicGeometry.Singularities.DltDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
public import MMP.AlgebraicGeometry.Divisor.GeneralMemberAdjunction
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChain.FlipWeightsOutsideBadSet
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepBranchesUnitDrop
public import Mathlib
public import MMP.Attr
import MMP.AlgebraicGeometry.Singularities.DltFloorComponentsNormal
import MMP.AlgebraicGeometry.Singularities.PltDifferentCoefficients

/-!
# Adjunction to the reduced component of a real plt pair

Let `X` be a `ℚ`-factorial normal complex variety, `S ⊂ X` a prime divisor and `Δ` an effective
`ℝ`-divisor without `S`-component such that `(X, S + Δ)` is plt. Write `Δ = ∑ δ_Q Q`. The
different is `Δ_S = B_S⁰ + ∑ δ_Q Q|_S`, where `B_S⁰` is the residue different of `K_X + S`
(`(div τ + S)|_S = div(Res_S τ) + B_S⁰` for a top form `τ` with a simple pole along `S`) and
`Q|_S` is the restriction of the `ℚ`-Cartier divisor `Q`. It satisfies
`(div τ + S + Δ)|_S = div(Res_S τ) + Δ_S` for every such `τ`, and it is the only `ℝ`-divisor on
`S` that does.

For a finite set `I ⊂ (0, 1)`, the numbers `1 - (1 - ∑_{b ∈ I} n_b b) / m` with `m ≥ 1`,
`n_b ∈ ℕ` and `∑ n_b b < 1` satisfy the descending chain condition: only finitely many sums
`∑ n_b b < 1` occur, since `n_b < 1 / b`, and the map `(t, m) ↦ 1 - (1 - t) / m` is monotone on
`{t < 1} × {m ≥ 1}`.

## Main results

* `MMP.Fourfold.exists_isNormal_isRCartierPullback_isPoincareResidue`: the coefficient sets
  are well-founded, `S` is normal, the different `Δ_S` exists, and every different is effective, klt, of hyperstandard coefficients,
  dominates `A|_S` and is monotone along nonpositive plt diagrams.

## Implementation notes

Pull-backs of `ℝ`-Cartier divisors along the closed immersion `S ⟶ X` are unique, since their
presentations only involve Cartier divisors not containing `S`. Changing the top form `τ` to
`b τ`, `b` a unit along `S`, changes `div τ` by the principal divisor `div b`, whose restriction
is `div b̄`, and the residue by `b̄`; so the residue identity for one form gives it for all.

The klt property of `(S, Δ_S)` is reduced to the rational case: components of `Δ` with
coefficient one do not meet `S`, and the remaining coefficient vector is a convex combination
of nearby rational vectors for which `S + ∑ b_Q Q` is still plt, while the klt region of `S`
along the `ℚ`-Cartier restrictions `Q|_S` is convex.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 16
-/

/-!
# Adjunction to the reduced component of a real plt pair

Let `X` be a `ℚ`-factorial normal complex variety of dimension `n + 1`, `S ⊂ X` a prime divisor
and `Δ` an effective `ℝ`-divisor not containing `S` such that `(X, S + Δ)` is a real plt pair:
`K_X + S + Δ` is `ℝ`-Cartier and every exceptional divisor over `X` has positive log
discrepancy. Then `S` is normal, and residue adjunction produces an effective `ℝ`-divisor `Δ_S`
on `S`, the different, with `K_S + Δ_S = (K_X + S + Δ)|_S` and `(S, Δ_S)` klt. When the positive
coefficients of `Δ` lie in a finite set `I ⊂ (0, 1)`, every coefficient of `Δ_S` has the form
`1 - (1 - ∑_{b ∈ I} n_b b) / m` with `m ≥ 1`, `n_b ∈ ℕ` and `∑ n_b b < 1`, and the set of these
numbers satisfies the descending chain condition. For an effective `ℚ`-Cartier `A ≤ Δ` not
containing `S`, `A|_S ≤ Δ_S`. Finally, adjunction is monotone along nonpositive diagrams: if
`(X', S' + Δ')` is a second such pair, `p : W ⟶ X`, `q : W ⟶ X'` proper birational with
`a(E; X, S + Δ) ≤ a(E; X', S' + Δ')` for every prime divisor `E` of `W`, and `S`, `S'` are the
images of one prime divisor of `W`, then `a(v; S, Δ_S) ≤ a(v; S', Δ_{S'})` for every divisorial
valuation `v` over the strict transform of `S` on `W`.

## Main results

* `MMP.Fourfold.exists_isNormal_isRCartierPullback_isPoincareResidue`

## Implementation notes

The canonical divisors are fixed by forms, as in residue adjunction: `K_X = div(τ)` for a
rational top form `τ` with `ord_S τ = -1`, so that `K_X + S + Δ` has no `S`-component, and
`K_S = div(ρ)` for the Poincaré residue `ρ = Res_S τ` (`MMP.Fourfold.IsPoincareResidue`). The
restriction of the `ℝ`-Cartier divisor `K_X + S + Δ` to `S` is its pull-back along the closed
immersion `S ⟶ X` (`MMP.Flips.IsRCartierPullback`). The equality is required for every such
`τ` and `ρ`; it determines `Δ_S`. The real plt and klt conditions are written out with the log
discrepancy `MMP.Intersection.IsLogDiscrepancy` of `ℝ`-divisors. A nonpositive diagram is given
by a common model `W` and the inequality of log discrepancies at the prime divisors of `W`, which
says that `p^*(K_X + S + Δ) - q^*(K_{X'} + S' + Δ')` is effective; the induced comparison on `S`
is stated for divisors over the strict transform `S_W` of `S`, through the induced birational
maps `S_W ⟶ S` and `S_W ⟶ S'`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 16
-/

@[expose] public section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Fourfold MMP.CyclicChartDifferent

namespace MMP.RealPltAdjunction

/-- **DCC of the hyperstandard-type coefficient set.** For a finite set `I ⊂ (0, 1)`, the set of
numbers `1 - (1 - ∑_{b ∈ I} n_b b) / m` with `m ≥ 1`, `n_b ∈ ℕ` and `∑ n_b b < 1` is
well-founded. -/
private theorem isWF_setOf_one_sub_div (I : Finset ℝ) (hI : ∀ b ∈ I, b ∈ Set.Ioo (0 : ℝ) 1) :
    Set.IsWF {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ ∃ c : ℝ → ℕ, ∑ b ∈ I, (c b : ℝ) * b < 1 ∧
        x = 1 - (1 - ∑ b ∈ I, (c b : ℝ) * b) / m} := by
  classical
  set M : ℕ := I.sup fun b => ⌈1 / b⌉₊
  let T : Set ℝ := {t | t < 1} ∩ Set.range fun k : I → Fin (M + 1) => ∑ b : I, (k b : ℝ) * b
  have hT : T.Finite := (Set.finite_range _).inter_of_right _
  have hsub : {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ ∃ c : ℝ → ℕ, ∑ b ∈ I, (c b : ℝ) * b < 1 ∧
        x = 1 - (1 - ∑ b ∈ I, (c b : ℝ) * b) / m} ⊆
      (fun p : ℝ × ℕ => 1 - (1 - p.1) / p.2) '' (T ×ˢ Set.Ici 1) := by
    rintro x ⟨m, hm, c, hc, rfl⟩
    refine ⟨(∑ b ∈ I, (c b : ℝ) * b, m), ⟨⟨hc, ?_⟩, hm⟩, rfl⟩
    have hle : ∀ b ∈ I, c b ≤ M := by
      intro b hb
      have hb0 := (hI b hb).1
      have h1 : (c b : ℝ) * b ≤ ∑ b ∈ I, (c b : ℝ) * b :=
        Finset.single_le_sum (f := fun b => (c b : ℝ) * b)
          (fun b hb => mul_nonneg (Nat.cast_nonneg _) (hI b hb).1.le) hb
      have h2 : (c b : ℝ) < 1 / b := by
        rw [lt_div_iff₀ hb0]; linarith
      have h3 : (c b : ℝ) < ⌈1 / b⌉₊ := h2.trans_le (Nat.le_ceil _)
      exact (Nat.cast_lt.mp h3).le.trans (Finset.le_sup (f := fun b => ⌈1 / b⌉₊) hb)
    refine ⟨fun b => ⟨c b, Nat.lt_succ_of_le (hle b b.2)⟩, ?_⟩
    simp only
    exact Finset.sum_coe_sort I (fun b => (c b : ℝ) * b)
  refine (Set.IsPWO.isWF ?_).mono hsub
  refine Set.IsPWO.image_of_monotoneOn (hT.isPWO.prod (Set.isPWO_of_wellQuasiOrderedLE _)) ?_
  rintro ⟨t, m⟩ ⟨⟨ht, -⟩, hm⟩ ⟨t', m'⟩ ⟨⟨ht', -⟩, hm'⟩ ⟨htt, hmm⟩
  simp only [Set.mem_Ici, Set.mem_setOf_eq] at *
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmm' : (m : ℝ) ≤ m' := by exact_mod_cast hmm
  have : (1 - t') / m' ≤ (1 - t) / m :=
    (div_le_div_of_nonneg_left (by linarith) hm0 hmm').trans
      (div_le_div_of_nonneg_right (by linarith) hm0.le)
  linarith

/-! ### Pull-backs of `ℝ`-Cartier divisors along an arbitrary morphism -/

section RPullback

open TensorProduct MMP.Flips

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- The Cartier divisors on `X` whose support misses the image of every generic point of `Y`,
those which can be pulled back along `f`. -/
private def cartierSubgroupAlong (f : Y ⟶ X) : AddSubgroup (Divisor X) where
  carrier := {L | L.IsCartier ∧ ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp}
  zero_mem' := ⟨Divisor.isCartier_zero, fun Z h => by
    rw [DivisorWithCoeffs.supp_zero] at h; exact h⟩
  add_mem' {L₁ L₂} h₁ h₂ := ⟨h₁.1.add h₂.1, fun Z h => by
    rcases DivisorWithCoeffs.supp_add_le L₁ L₂ h with h | h
    · exact h₁.2 Z h
    · exact h₂.2 Z h⟩
  neg_mem' {L} h := ⟨h.1.neg, fun Z h' => h.2 Z (by rwa [DivisorWithCoeffs.supp_neg] at h')⟩

/-- Pull-back along `f`, on the Cartier divisors which can be pulled back. -/
private noncomputable def cartierPullbackHomAlong [CompactSpace Y] (f : Y ⟶ X) :
    cartierSubgroupAlong f →+ Divisor Y where
  toFun L := (L : Divisor X).pullback L.2.1 L.2.2
  map_zero' := Divisor.IsPullback.pullback_eq Divisor.isCartier_zero (Divisor.isPullback_zero _)
  map_add' L₁ L₂ := Divisor.IsPullback.pullback_eq (L₁ + L₂).2.1
    (Divisor.IsPullback.add L₁.2.1 L₂.2.1 _ (Divisor.isPullback_pullback _ _)
      (Divisor.isPullback_pullback _ _))

private theorem rDivisorTensorMap_cartierSubgroupAlong_injective (f : Y ⟶ X) :
    Function.Injective (rDivisorTensorMap (cartierSubgroupAlong f).subtype) :=
  (Divisor.tensorEquiv ℝ X).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)

/-- **Uniqueness of the pull-back of an `ℝ`-Cartier divisor** along an arbitrary morphism (the
presentations in `MMP.Flips.IsRCartierPullback` only use Cartier divisors which can be pulled
back). -/
private theorem isRCartierPullback_eq [CompactSpace Y] (f : Y ⟶ X) {D : RDivisor X}
    {G₁ G₂ : RDivisor Y} (h₁ : IsRCartierPullback f D G₁) (h₂ : IsRCartierPullback f D G₂) :
    G₁ = G₂ := by
  have key : ∀ {G : RDivisor Y}, IsRCartierPullback f D G →
      ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → cartierSubgroupAlong f),
        D = ∑ j, r j • Divisor.toRDivisor (L j : Divisor X) ∧
        G = rDivisorTensorMap (cartierPullbackHomAlong f) (∑ j, L j ⊗ₜ[ℤ] r j) := by
    intro G hG
    obtain ⟨m, r, L, L', hL, rfl, hL', rfl⟩ := hG
    refine ⟨m, r, fun j => ⟨L j, hL j, (hL' j).1⟩, rfl, ?_⟩
    simp only [map_sum, rDivisorTensorMap_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨hB, hp⟩ := hL' j
    congr 2
    exact (Divisor.IsPullback.pullback_eq (hL j) hp).symm
  obtain ⟨m, r, L, hD₁, rfl⟩ := key h₁
  obtain ⟨p, s, M, hD₂, rfl⟩ := key h₂
  congr 1
  apply rDivisorTensorMap_cartierSubgroupAlong_injective f
  simp only [map_sum, rDivisorTensorMap_tmul, AddSubgroup.coe_subtype]
  exact hD₁.symm.trans hD₂

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is its pull-back as an `ℝ`-Cartier divisor. -/
private theorem isRCartierPullback_of_isPullback (f : Y ⟶ X) {B : QDivisor X}
    (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp}
    {B' : QDivisor Y} (h : B.IsPullback f hB B') :
    IsRCartierPullback f (QDivisor.toRDivisor B) (QDivisor.toRDivisor B') := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hBq.exists_pos
  obtain ⟨D', hD', hp⟩ := h m hm D hD hDc
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => D, fun _ => D', fun _ => hDc, ?_, fun _ => ⟨_, hp⟩,
    ?_⟩ <;> rw [Fin.sum_univ_one] <;> ext E
  · have := congrArg (fun G : QDivisor X => G.coeff E) hD
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul,
      Int.cast_natCast] at this
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    rw [show ((D.coeff E : ℤ) : ℝ) = ((D.coeff E : ℚ) : ℝ) by push_cast; rfl, this]
    push_cast; field_simp
  · have := congrArg (fun G : QDivisor Y => G.coeff E) hD'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul,
      Int.cast_natCast] at this
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    rw [show ((D'.coeff E : ℤ) : ℝ) = ((D'.coeff E : ℚ) : ℝ) by push_cast; rfl, this]
    push_cast; field_simp

end RPullback

/-! ### Changing the top form -/

section ChangeOfForm

variable {X T : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- A unit of a stalk of an integral scheme, as a unit of the ring of rational functions. -/
private noncomputable def unitOfStalk {x : X} (b : (X.presheaf.stalk x)ˣ) :
    (RationalFunctions X)ˣ :=
  (RationalFunctions.unitsEquiv X).symm fun Z =>
    Units.map (X.presheaf.stalkSpecializes (show componentGenericPoint X Z ⤳ x from
      (componentGenericPoint_eq_genericPoint Z) ▸ genericPoint_specializes x)).hom.toMonoidHom b

private theorem ord_unitOfStalk {x : X} (b : (X.presheaf.stalk x)ˣ) (E : Mori.PrimeDivisor X) :
    E.ord (unitOfStalk b) =
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField b) E.genericPoint := by
  rw [MMP.Positivity.ord_eq_ord_componentToFunctionField]
  exact congrArg (fun z => X.ord z E.genericPoint)
    (Aux.componentToFunctionField_stalkSpecializes X _ _ _)

/-- A unit of the stalk at `x` has order zero along every prime divisor through `x`. -/
private theorem ord_algebraMap_unit_eq_zero {x : X} (b : (X.presheaf.stalk x)ˣ)
    (E : Mori.PrimeDivisor X) (hx : x ∈ E.support) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField b) E.genericPoint = 0 := by
  have h1 := ord_nonneg_of_mem_support E hx (b : X.presheaf.stalk x)
  have h2 := ord_nonneg_of_mem_support E hx ((b⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x)
  have hne : ∀ c : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField (c : X.presheaf.stalk x) ≠ 0 :=
    fun c => (c.isUnit.map _).ne_zero
  have h3 := Scheme.ord_mul (x := E.genericPoint) (hne b) (hne b⁻¹)
  rw [← map_mul, Units.mul_inv, map_one, Aux.ord_one'] at h3
  omega

variable [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]

/-- The principal divisor of a unit `b` of `𝒪_{X, j(η_T)}` misses the generic point of `T`. -/
private theorem map_componentGenericPoint_notMem_supp_unitOfStalk (j : T ⟶ X)
    (b : (X.presheaf.stalk (j (genericPoint T)))ˣ) (Z : irreducibleComponents T) :
    j (componentGenericPoint T Z) ∉ (Mori.principalDivisor (unitOfStalk b)).supp := by
  intro h
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [componentGenericPoint_eq_genericPoint] at hmem
  exact hE (by rw [coeff_principalDivisor, ord_unitOfStalk, ord_algebraMap_unit_eq_zero b E hmem])

/-- The pull-back of the principal divisor of a unit `b` of `𝒪_{X, j(η_T)}` along `j` is the
divisor of its restriction `b̄ ∈ k(T)`. -/
private theorem coeff_principalDivisor_pullbackRationalFunction_unitOfStalk (j : T ⟶ X)
    (b : (X.presheaf.stalk (j (genericPoint T)))ˣ) (Q : Mori.PrimeDivisor T) :
    (Mori.principalDivisor (pullbackRationalFunction j (unitOfStalk b)
      (map_componentGenericPoint_notMem_supp_unitOfStalk j b))).coeff Q =
      T.ord ((j.stalkMap (genericPoint T)).hom b) Q.genericPoint := by
  have key : ∀ (ζ : T) (_ : ζ = genericPoint T), ∃ a : (X.presheaf.stalk (j ζ))ˣ,
      (∀ (y : X) (h : y ⤳ j ζ) (h' : y ⤳ j (genericPoint T)),
        (X.presheaf.stalkSpecializes h).hom a = (X.presheaf.stalkSpecializes h').hom b) ∧
      algebraMap (T.presheaf.stalk ζ) T.functionField ((j.stalkMap ζ).hom a) =
        (j.stalkMap (genericPoint T)).hom b := by
    rintro ζ rfl
    exact ⟨b, fun _ _ _ => rfl, Aux.algebraMap_stalk_genericPoint T _⟩
  obtain ⟨a, ha1, ha2⟩ := key _ (componentGenericPoint_eq_genericPoint Q.component)
  rw [coeff_principalDivisor, PrimeDivisor.ord_eq_ordUnit]
  have hc : Units.map (RationalFunctions.component T Q.component).toMonoidHom
      (pullbackRationalFunction j (unitOfStalk b)
        (map_componentGenericPoint_notMem_supp_unitOfStalk j b)) =
      Units.map (j.stalkMap (componentGenericPoint T Q.component)).hom.toMonoidHom a := by
    ext
    refine (congrArg Units.val (pullbackComponent_eq
      (map_componentGenericPoint_notMem_supp_unitOfStalk j b)
      (Divisor.isLocalEquation_principalDivisor (unitOfStalk b) ⊤) (Z := Q.component) trivial
      (mem_pointComponent (j (componentGenericPoint T Q.component))) a ?_) :)
    exact ha1 _ _ _
  rw [hc, Aux.ordUnit_eq_ord]
  exact congrArg (fun z => T.ord z Q.genericPoint) ha2

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral T]
  [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] in
/-- **The residue different does not depend on the form.** If `τ₀`, `τ` are rational top forms
with a simple pole along `S` and `ρ₀`, `ρ` their Poincaré residues, then
`(div τ + D)|_S = div ρ + G` as soon as `(div τ₀ + D)|_S = div ρ₀ + G`: indeed `τ = b τ₀` for a
unit `b` along `S`, `ρ = b̄ ρ₀`, and `(div b)|_S = div b̄`. -/
private theorem isRCartierPullback_divisorOfForm_of_isPoincareResidue
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    {τ τ₀ : RationalPluriForms sX (n + 1) 1} (hτ0 : τ ≠ 0) (hτ₀0 : τ₀ ≠ 0)
    (hτ : P.ordForm τ = -1) (hτ₀ : P.ordForm τ₀ = -1)
    {ρ ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀) {D : RDivisor X} {G : RDivisor T}
    (h : MMP.Flips.IsRCartierPullback j (Divisor.toRDivisor (divisorOfForm τ₀) + D)
      (Divisor.toRDivisor (divisorOfForm ρ₀) + G)) :
    MMP.Flips.IsRCartierPullback j (Divisor.toRDivisor (divisorOfForm τ) + D)
      (Divisor.toRDivisor (divisorOfForm ρ) + G) := by
  haveI : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (j ≫ sX)
  have hjT := Aux.map_genericPoint_eq j P hP
  obtain ⟨b, hτb, hres⟩ :=
    MMP.Fourfold.IsPoincareResidue.exists_unit_smul hdim P hjT hτ0 hτ₀0 (hτ.trans hτ₀.symm) hρ
  set ψ := (j.stalkMap (genericPoint T)).hom
  have hρ₀eq : ρ₀ = ψ ((b⁻¹ : (X.presheaf.stalk (j (genericPoint T)))ˣ) : _) • ρ :=
    IsPoincareResidue.unique_of_isClosedImmersion P hjT hρ₀ hres
  have hρeq : ρ = ψ (b : X.presheaf.stalk (j (genericPoint T))) • ρ₀ := by
    rw [hρ₀eq, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
  have hd : (Algebra.trdeg ℂ X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg ℂ T.functionField).toNat = n := by
    have := Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  have hb0 : algebraMap _ X.functionField (b : X.presheaf.stalk (j (genericPoint T))) ≠ 0 :=
    (b.isUnit.map _).ne_zero
  have hψb0 : ψ (b : X.presheaf.stalk (j (genericPoint T))) ≠ 0 := (b.isUnit.map _).ne_zero
  -- `div τ = div τ₀ + div b`
  have hX1 : divisorOfForm τ = divisorOfForm τ₀ + Mori.principalDivisor (unitOfStalk b) := by
    ext E
    change (divisorOfForm τ).coeff E = (divisorOfForm τ₀).coeff E +
      (Mori.principalDivisor (unitOfStalk b)).coeff E
    rw [coeff_divisorOfForm, coeff_divisorOfForm, coeff_principalDivisor, ord_unitOfStalk, hτb,
      E.ordForm_smul hd hb0 hτ₀0, add_comm]
  -- `div ρ = div ρ₀ + div b̄`
  have hT1 : divisorOfForm ρ = divisorOfForm ρ₀ + Mori.principalDivisor (pullbackRationalFunction j
      (unitOfStalk b) (map_componentGenericPoint_notMem_supp_unitOfStalk j b)) := by
    ext Q
    change (divisorOfForm ρ).coeff Q = (divisorOfForm ρ₀).coeff Q + (Mori.principalDivisor _).coeff Q
    have hρ₀0 : ρ₀ ≠ 0 :=
      Aux.isPoincareResidue_ne_zero sX hX hdim j hT P hP τ₀ hτ₀0 hτ₀ ρ₀ hρ₀ Q
    rw [coeff_divisorOfForm, coeff_divisorOfForm,
      coeff_principalDivisor_pullbackRationalFunction_unitOfStalk, hρeq,
      Q.ordForm_smul hdT hψb0 hρ₀0, add_comm]
  have hpb := MMP.Fourfold.isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor _)
    (map_componentGenericPoint_notMem_supp_unitOfStalk j b)
    (Divisor.isPullback_principalDivisor (unitOfStalk b) _)
  convert MMP.Fourfold.isRCartierPullback_add h hpb using 1
  · rw [hX1, map_add]; abel
  · rw [hT1, map_add]; abel

end ChangeOfForm

/-- The divisor of a nonzero top form on a normal variety is canonical. -/
private theorem isCanonicalDivisor_divisorOfForm {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n)
    {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n := by
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sX hX hdim
  exact hK.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ)

/-- A component of an `ℝ`-divisor without `P`-component is not `P`. -/
private theorem ne_of_mem_support {X : Scheme.{0}} {Δ : RDivisor X} {P Q : Mori.PrimeDivisor X}
    (hΔP : Δ.coeff P = 0) (hQ : Q ∈ Δ.support) : Q ≠ P := by
  rintro rfl
  exact Finsupp.mem_support_iff.mp hQ hΔP

/-! ### The real different -/

section Different

variable {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
  [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
  (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
  [CompactSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))

include hP in
/-- On a `ℚ`-factorial `X`, every prime divisor `Q ≠ S` restricts to `S`, effectively. -/
private theorem exists_restrict_primeDivisor (hQ : IsQFactorial sX) :
    ∃ R : Mori.PrimeDivisor X → QDivisor T, ∀ Q, Q ≠ P → R Q ≥ 0 ∧
      ∃ hgen : ∀ Z : irreducibleComponents T,
          j (componentGenericPoint T Z) ∉ DivisorWithCoeffs.supp (Finsupp.single Q (1 : ℚ) : QDivisor X),
        QDivisor.IsPullback j (Finsupp.single Q (1 : ℚ) : QDivisor X) hgen (R Q) := by
  classical
  have hgen : ∀ Q, Q ≠ P → ∀ Z : irreducibleComponents T,
      j (componentGenericPoint T Z) ∉ DivisorWithCoeffs.supp (Finsupp.single Q (1 : ℚ) : QDivisor X) :=
    fun Q hQP => map_componentGenericPoint_notMem_supp j P hP (Finsupp.single_eq_of_ne hQP.symm)
  refine ⟨fun Q => if hQP : Q = P then 0 else
    QDivisor.pullback _ (isQCartier_of_isQFactorial sX hQ _) (hgen Q hQP), fun Q hQP => ?_⟩
  simp only [dif_neg hQP]
  refine ⟨fun E => ?_, hgen Q hQP, QDivisor.isPullback_pullback _ _⟩
  obtain ⟨m, hm, D, hD, hDc⟩ := (isQCartier_of_isQFactorial sX hQ
    (Finsupp.single Q (1 : ℚ) : QDivisor X)).exists_pos
  obtain ⟨D', hD', hp⟩ := QDivisor.isPullback_pullback (f := j)
    (isQCartier_of_isQFactorial sX hQ _) (hgen Q hQP) m hm D hD hDc
  have hDnn : ∀ G : Mori.PrimeDivisor X, 0 ≤ D.coeff G := fun G => by
    have := congrArg (fun B : QDivisor X => B.coeff G) hD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    have h0 : (0 : ℚ) ≤ ((m : ℤ) : ℚ) * DivisorWithCoeffs.coeff (Finsupp.single Q (1 : ℚ) : QDivisor X) G :=
      mul_nonneg (by positivity) (by
        change (0 : ℚ) ≤ (Finsupp.single Q (1 : ℚ)) G
        rw [Finsupp.single_apply]; split_ifs <;> norm_num)
    exact_mod_cast this ▸ h0
  have h1 := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hDc (V := ⊤)
    (fun G _ => hDnn G) hp E ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
  have := congrArg (fun B : QDivisor T => B.coeff E) hD'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
  have hm' : (0 : ℚ) < ((m : ℤ) : ℚ) := by exact_mod_cast hm
  have h2 : (0 : ℚ) ≤ ((m : ℤ) : ℚ) * (QDivisor.pullback _ (isQCartier_of_isQFactorial sX hQ _)
      (hgen Q hQP) : QDivisor T).coeff E := by
    rw [← this]; exact_mod_cast h1
  exact (mul_nonneg_iff_of_pos_left hm').mp h2

omit [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] in
private theorem toRDivisor_single_one (Q : Mori.PrimeDivisor X) :
    QDivisor.toRDivisor (Finsupp.single Q (1 : ℚ) : QDivisor X) = Finsupp.single Q 1 := by
  classical
  ext E
  change ((Finsupp.single Q (1 : ℚ) E : ℚ) : ℝ) = Finsupp.single Q (1 : ℝ) E
  rw [Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

omit [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] in
private theorem sum_coeff_smul_single_eq (Δ : RDivisor X) :
    ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (Finsupp.single Q (1 : ℚ) : QDivisor X) =
      Δ := by
  simp_rw [toRDivisor_single_one, Finsupp.smul_single_one]
  exact Finsupp.sum_single Δ

/-- **Restriction of a combination of prime divisors.** If `R_Q = Q|_S` for `Q ≠ S`, then
`∑ c_Q R_Q` is the pull-back of `∑ c_Q Q` for any real `c` and any components `Q ≠ S`. -/
private theorem isRCartierPullback_sum_smul_restrict (hQ : IsQFactorial sX)
    {R : Mori.PrimeDivisor X → QDivisor T}
    (hR : ∀ Q, Q ≠ P → R Q ≥ 0 ∧
      ∃ hgen : ∀ Z : irreducibleComponents T,
          j (componentGenericPoint T Z) ∉ DivisorWithCoeffs.supp (Finsupp.single Q (1 : ℚ) : QDivisor X),
        QDivisor.IsPullback j (Finsupp.single Q (1 : ℚ) : QDivisor X) hgen (R Q))
    (s : Finset (Mori.PrimeDivisor X)) (hs : ∀ Q ∈ s, Q ≠ P) (c : Mori.PrimeDivisor X → ℝ) :
    MMP.Flips.IsRCartierPullback j
      (∑ Q ∈ s, c Q • QDivisor.toRDivisor (Finsupp.single Q (1 : ℚ) : QDivisor X))
      (∑ Q ∈ s, c Q • QDivisor.toRDivisor (R Q)) :=
  MMP.Fourfold.isRCartierPullback_sum _ _ _ fun Q hQs => MMP.Fourfold.isRCartierPullback_smul _
    (isRCartierPullback_of_isPullback j (isQCartier_of_isQFactorial sX hQ _)
      (hR Q (hs Q hQs)).2.2)

include hP in
/-- A divisor `div τ + S + B`, with `τ` of order `-1` along `S` and `B` without `S`-component, does
not contain `S`. -/
private theorem map_componentGenericPoint_notMem_supp_divisorOfForm_add {n : ℕ}
    {τ : RationalPluriForms sX (n + 1) 1} (hτ : P.ordForm τ = -1) {B : QDivisor X}
    (hBP : B.coeff P = 0) (Z : irreducibleComponents T) :
    j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B : QDivisor X).supp :=
  map_componentGenericPoint_notMem_supp j P hP (by
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
      coeff_divisorOfForm, hτ, hBP, DivisorWithCoeffs.coeff_apply, Finsupp.single_eq_same]
    norm_num) Z

include hP in
/-- **The residue identity for the real different.** With `B_S⁰` the residue different of
`K_X + S` (`(div τ₀ + S)|_S = div ρ₀ + B_S⁰`) and `R_Q = Q|_S`, the divisor
`Δ_S = B_S⁰ + ∑ δ_Q R_Q` satisfies `(div τ + S + Δ)|_S = div ρ + Δ_S` for every form `τ` with a
simple pole along `S` and its residue `ρ`. -/
private theorem isRCartierPullback_residueDifferent (hX : IsNormalVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = n + 1) (hT : IsNormalVariety ℂ (j ≫ sX))
    (hQ : IsQFactorial sX) {Δ : RDivisor X} (hΔP : Δ.coeff P = 0)
    {R : Mori.PrimeDivisor X → QDivisor T}
    (hR : ∀ Q, Q ≠ P → R Q ≥ 0 ∧
      ∃ hgen : ∀ Z : irreducibleComponents T,
          j (componentGenericPoint T Z) ∉ DivisorWithCoeffs.supp (Finsupp.single Q (1 : ℚ) : QDivisor X),
        QDivisor.IsPullback j (Finsupp.single Q (1 : ℚ) : QDivisor X) hgen (R Q))
    {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0) (hτ₀ : P.ordForm τ₀ = -1)
    {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀)
    {BS₀ : QDivisor T}
    (hBS₀ : ∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
        (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + 0 : QDivisor X).supp,
      (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + 0 : QDivisor X).IsPullback j
        hgen (Divisor.toQDivisor (divisorOfForm ρ₀) + BS₀))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ) :
    MMP.Flips.IsRCartierPullback j
      (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P 1 + Δ)
      (Divisor.toRDivisor (divisorOfForm ρ) +
        (QDivisor.toRDivisor BS₀ + ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q))) := by
  rw [add_assoc]
  refine isRCartierPullback_divisorOfForm_of_isPoincareResidue sX hX hdim j hT P hP hτ0 hτ₀0 hτ
    hτ₀ hρ hρ₀ ?_
  obtain ⟨hgen, hpb⟩ := hBS₀
  have h1 := isRCartierPullback_of_isPullback j (isQCartier_of_isQFactorial sX hQ _) hpb
  have h2 := isRCartierPullback_sum_smul_restrict sX j P hQ hR Δ.support
    (fun _ => ne_of_mem_support hΔP) Δ.coeff
  rw [sum_coeff_smul_single_eq] at h2
  convert MMP.Fourfold.isRCartierPullback_add h1 h2 using 1
  · rw [map_add, map_add, map_zero, add_zero, QDivisor.toRDivisor_toQDivisor, toRDivisor_single_one,
      add_assoc]
  · rw [map_add, QDivisor.toRDivisor_toQDivisor, add_assoc]

omit [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [IsIntegral T]
  [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T] in
private theorem coeff_residueDifferent (BS₀ : QDivisor T) (R : Mori.PrimeDivisor X → QDivisor T)
    (Δ : RDivisor X) (E : Mori.PrimeDivisor T) :
    (QDivisor.toRDivisor BS₀ + ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q)).coeff E =
      (BS₀.coeff E : ℝ) + ∑ Q ∈ Δ.support, Δ.coeff Q * ((R Q).coeff E : ℝ) := by
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  rfl

omit [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [IsIntegral T]
  [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T] in
/-- The real different `B_S⁰ + ∑ δ_Q R_Q` is effective. -/
private theorem isEffective_residueDifferent {BS₀ : QDivisor T} (hBS₀ : BS₀.IsEffective)
    {R : Mori.PrimeDivisor X → QDivisor T} {Δ : RDivisor X} (hΔ : ∀ Q, 0 ≤ Δ.coeff Q)
    (hΔP : Δ.coeff P = 0) (hR : ∀ Q, Q ≠ P → R Q ≥ 0) :
    (QDivisor.toRDivisor BS₀ + ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q)).IsEffective := by
  intro E
  rw [coeff_residueDifferent]
  refine add_nonneg (by exact_mod_cast hBS₀ E) (Finset.sum_nonneg fun Q hQΔ => ?_)
  exact mul_nonneg (hΔ Q) (by exact_mod_cast hR Q (ne_of_mem_support hΔP hQΔ) E)

include hP in
/-- **The different contains `A|_S`.** For an effective `ℚ`-Cartier `A ≤ Δ` not containing `S`,
`A|_S = ∑ a_Q R_Q`, so `Δ_S - A|_S = B_S⁰ + ∑ (δ_Q - a_Q) R_Q ≥ 0`. -/
private theorem coeff_isPullback_le_residueDifferent (hQ : IsQFactorial sX) {BS₀ : QDivisor T}
    (hBS₀ : BS₀.IsEffective) {Δ : RDivisor X} (hΔP : Δ.coeff P = 0)
    {R : Mori.PrimeDivisor X → QDivisor T}
    (hR : ∀ Q, Q ≠ P → R Q ≥ 0 ∧
      ∃ hgen : ∀ Z : irreducibleComponents T,
          j (componentGenericPoint T Z) ∉ DivisorWithCoeffs.supp (Finsupp.single Q (1 : ℚ) : QDivisor X),
        QDivisor.IsPullback j (Finsupp.single Q (1 : ℚ) : QDivisor X) hgen (R Q))
    (A : QDivisor X) (hA : A.IsEffective) (hAq : A.IsQCartier)
    (hAΔ : ∀ Q, (A.coeff Q : ℝ) ≤ Δ.coeff Q)
    (hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ A.supp)
    (AS : QDivisor T) (hAS : A.IsPullback j hgen AS) (E : Mori.PrimeDivisor T) :
    (AS.coeff E : ℝ) ≤
      (QDivisor.toRDivisor BS₀ + ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q)).coeff E := by
  classical
  have hQP : ∀ Q ∈ Δ.support, Q ≠ P := fun _ => ne_of_mem_support hΔP
  -- `A = ∑_{Q ∈ Supp Δ} a_Q Q`
  have hAeq : ∑ Q ∈ Δ.support, ((A.coeff Q : ℚ) : ℝ) •
      QDivisor.toRDivisor (Finsupp.single Q (1 : ℚ) : QDivisor X) = QDivisor.toRDivisor A := by
    have hsub : A.support ⊆ Δ.support := fun Q hQ => by
      rw [Finsupp.mem_support_iff] at hQ ⊢
      intro h0
      have h1 := hAΔ Q
      have h2 := hA Q
      rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, h0] at *
      exact hQ (by exact_mod_cast le_antisymm h1 (by exact_mod_cast h2))
    rw [← Finset.sum_subset hsub fun Q _ hQ => by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hQ]; simp]
    ext G
    simp only [toRDivisor_single_one, Finsupp.smul_single_one]
    change (∑ x ∈ A.support, Finsupp.single x ((A.coeff x : ℚ) : ℝ)) G = ((A G : ℚ) : ℝ)
    rw [Finsupp.finset_sum_apply]
    by_cases hG : G ∈ A.support
    · rw [Finset.sum_eq_single G (fun b _ hb => Finsupp.single_eq_of_ne hb.symm)
        (fun h => absurd hG h), Finsupp.single_eq_same]; rfl
    · rw [Finset.sum_eq_zero fun b hb => Finsupp.single_eq_of_ne (fun h : G = b => hG (by rw [h]; exact hb)),
        Finsupp.notMem_support_iff.mp hG]; simp
  have h1 := isRCartierPullback_of_isPullback j hAq hAS
  have h2 : MMP.Flips.IsRCartierPullback j (QDivisor.toRDivisor A)
      (∑ Q ∈ Δ.support, ((A.coeff Q : ℚ) : ℝ) • QDivisor.toRDivisor (R Q)) := by
    rw [← hAeq]
    exact isRCartierPullback_sum_smul_restrict sX j P hQ hR _ hQP _
  have h3 := congrArg (fun G : RDivisor T => G.coeff E) (isRCartierPullback_eq j h1 h2)
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul] at h3
  have h3' : ((AS.coeff E : ℚ) : ℝ) =
      ∑ Q ∈ Δ.support, ((A.coeff Q : ℚ) : ℝ) * (((R Q).coeff E : ℚ) : ℝ) := h3
  rw [coeff_residueDifferent, h3']
  have hle : ∑ Q ∈ Δ.support, ((A.coeff Q : ℚ) : ℝ) * (((R Q).coeff E : ℚ) : ℝ) ≤
      ∑ Q ∈ Δ.support, Δ.coeff Q * ((R Q).coeff E : ℝ) :=
    Finset.sum_le_sum fun Q hQΔ => mul_le_mul_of_nonneg_right (hAΔ Q)
      (by exact_mod_cast (hR Q (hQP Q hQΔ)).1 E)
  have hB : (0 : ℝ) ≤ (BS₀.coeff E : ℝ) := by exact_mod_cast hBS₀ E
  linarith

include hP in
omit [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T] [CompactSpace X] in
/-- A prime divisor of a variety of dimension `n + 1` has dimension `n`. -/
private theorem topologicalKrullDim_eq_of_isClosedImmersion {n : ℕ}
    (hdim : topologicalKrullDim X = n + 1) [LocallyOfFiniteType (j ≫ sX)] :
    topologicalKrullDim T = n := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (j ≫ sX)
  have hjT := Aux.map_genericPoint_eq j P hP
  have hd : (Algebra.trdeg ℂ X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have := Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
  rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (j ≫ sX)]
  norm_cast
  omega

end Different

/-! ### Rational sub-boundaries of a real plt pair -/

section SubBoundary

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsNormal X]
  [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A Kollár–Mori discrepancy depends only on the valuation of the divisor. -/
private theorem isDiscrepancy_of_valuation_eq' (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {D D' : DivisorOver ℂ sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) (hv : D.valuation = D'.valuation) :
    IsDiscrepancy sX n K Δ D' a := by
  obtain ⟨-, hK, m, hm, hC, U, hU, τ, hτ, hτa⟩ := ha
  refine ⟨hX, hK, m, hm, hC, U,
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv ▸ hU, τ, hτ, ?_⟩
  rw [hτa, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
    hK.topologicalKrullDim_eq hv τ]

omit [IsIntegral X] [CompactSpace X] [LocallyOfFiniteType sX] in
private theorem isCartierCombination_of_isRCartier {D : RDivisor X}
    (h : RDivisor.IsRCartier D) : MMP.Flips.IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := h
  refine ⟨m, r, C, hC, ?_⟩
  ext Γ
  change D.coeff Γ = (∑ j, r j • (C j).mapCoeffs (Int.cast : ℤ → ℝ) Int.cast_zero).coeff Γ
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  rw [MMP.Flips.coeff_sum_smul_toRDivisor]
  exact hD Γ

/-- **Lowering the boundary raises log discrepancies.** On a `ℚ`-factorial variety, if `B ≤ Δ`
then `a(E; X, Δ) ≤ a(E; X, B)`: the difference is the coefficient of the effective pull-back of
the `ℝ`-Cartier divisor `Δ - B`. -/
private theorem isLogDiscrepancy_le_of_le (hX : IsQFactorial sX) {Δ B : RDivisor X}
    (hle : ∀ P, B.coeff P ≤ Δ.coeff P) {n n' : ℕ} {E : DivisorOver ℂ sX} {a a' : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n B E a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sX n' Δ E a') : a' ≤ a := by
  classical
  obtain ⟨hXn, hprop, ω, hω, hKω, m, r, L, L', hL, hsum, hpb, rfl⟩ := ha
  obtain ⟨m₂, s, M, hM, hMsum⟩ := hX.isRCartier (Δ - B)
  haveI := E.isIntegral
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isDominant
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose M' hM' using fun j => (hM j).exists_isPullback
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j))
  have hMpb : ∀ j, ∃ h, (M j).IsPullback E.f h (M' j) := fun j =>
    ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j), hM' j⟩
  have hb : MMP.Intersection.IsLogDiscrepancy sX n Δ E _ := ⟨hXn, hprop, ω, hω, hKω, m + m₂,
    Fin.append r s, Fin.append L M, Fin.append L' M',
    Fin.addCases (fun i => by simpa using hL i) (fun j => by simpa using hM j),
    fun Γ => ?_, Fin.addCases (fun i => by simpa using hpb i)
      (fun j => by simpa using hMpb j), rfl⟩
  · rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha' hb, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have heff := (isEffective_of_isRCartierPullback E.f ⟨m₂, s, M, hM, hMsum⟩
      fun P => sub_nonneg.mpr (hle P)).2
      (∑ j, s j • Divisor.toRDivisor (M' j))
      ⟨m₂, s, M, M', hM, by ext P; rw [hMsum P, coeff_sum_smul_toRDivisor], hMpb, rfl⟩
    have hE := heff E.E
    rw [show (∑ j, s j • Divisor.toRDivisor (M' j)) E.E =
      (∑ j, s j • Divisor.toRDivisor (M' j)).coeff E.E from rfl,
      coeff_sum_smul_toRDivisor] at hE
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hE
    linarith
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have h1 := hsum Γ
    have h2 := hMsum Γ
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Pi.sub_apply] at h1 h2 ⊢
    linarith

/-- **Discrepancies from log discrepancies.** If every exceptional divisor over `X` with a
proper model has positive log discrepancy for the `ℚ`-divisor `B`, then every exceptional
divisor over `X` has discrepancy `> -1` for `B`: pass to a proper model with the same valuation
and use `a = 1 + d`. -/
private theorem neg_one_lt_of_isDiscrepancy_of_pos (hX : IsNormalVariety ℂ sX) {B : QDivisor X}
    (hpos : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (QDivisor.toRDivisor B) E a → 0 < a)
    {n : ℕ} {K : Divisor X} (D : DivisorOver ℂ sX) (hD : D.IsExceptional) (a : ℚ)
    (ha : IsDiscrepancy sX n K B D a) : -1 < a := by
  obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D
  have haE := isDiscrepancy_of_valuation_eq' hX ha hE.symm
  have h1 := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy haE (1 + a)).mpr
    ⟨E.isProper, rfl⟩
  have hexc : E.toDivisorOver.IsExceptional := by
    rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight
      hX] at hD ⊢
    rwa [MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hE]
  have hpos' := hpos n E.toDivisorOver _ hexc h1
  have : (-1 : ℝ) < (a : ℝ) := by linarith
  exact_mod_cast this

/-- **Lowering a real plt boundary.** If every exceptional divisor over the `ℚ`-factorial `X`
has positive log discrepancy for `Δ'`, the same holds for every `ℝ`-divisor `B ≤ Δ'`. -/
private theorem pos_of_isLogDiscrepancy_of_le_of_isExceptional (hQ : IsQFactorial sX)
    {Δ' B : RDivisor X} (hle : ∀ P, B.coeff P ≤ Δ'.coeff P)
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m Δ' E a → 0 < a)
    (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ) (hE : E.IsExceptional)
    (ha : MMP.Intersection.IsLogDiscrepancy sX m B E a) : 0 < a := by
  obtain ⟨-, hprop, -, -, ⟨K, hK, -⟩, -⟩ := id ha
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hQ.1 hK
  have hdivω : divisorOfForm ω = K := by
    ext Γ
    exact hω Γ
  obtain ⟨a', ha'⟩ := MMP.Fourfold.exists_isLogDiscrepancy hQ.1 hω0 (hdivω ▸ hK)
    (isCartierCombination_of_isRCartier (hQ.isRCartier _)) E hprop
  have := hplt m E a' hE ha'
  have := isLogDiscrepancy_le_of_le hQ hle ha ha'
  linarith

/-- **Discrepancies of a rational sub-boundary.** If every exceptional divisor over `X` has
positive log discrepancy for `Δ'`, then every exceptional divisor has discrepancy `> -1` for
any `ℚ`-divisor `B ≤ Δ'`. -/
private theorem neg_one_lt_of_isDiscrepancy (hQ : IsQFactorial sX) {Δ' : RDivisor X}
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m Δ' E a → 0 < a)
    {B : QDivisor X} (hBΔ : ∀ Q, (B.coeff Q : ℝ) ≤ Δ'.coeff Q) {n : ℕ} {K : Divisor X}
    (D : DivisorOver ℂ sX) (hD : D.IsExceptional) (a : ℚ)
    (ha : IsDiscrepancy sX n K B D a) : -1 < a :=
  neg_one_lt_of_isDiscrepancy_of_pos hQ.1
    (pos_of_isLogDiscrepancy_of_le_of_isExceptional hQ (fun Q => by simpa using hBΔ Q) hplt)
    D hD a ha

/-- **Rational sub-boundaries of a real plt pair are dlt.** If every exceptional divisor over the
`ℚ`-factorial variety `X` has positive log discrepancy for `S + Δ`, and `0 ≤ B ≤ Δ` is a
`ℚ`-divisor with coefficients `< 1` and no `S`-component, then `(X, S + B)` is dlt: off an open
containing all codimension-one points it is snc. -/
private theorem isDltPair_add_single (hQ : IsQFactorial sX) {P : Mori.PrimeDivisor X}
    {Δ : RDivisor X}
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) E a → 0 < a)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (B : QDivisor X) (hB0 : 0 ≤ B) (hBP : B.coeff P = 0) (hB1 : ∀ Q, B.coeff Q < 1)
    (hBΔ : ∀ Q, (B.coeff Q : ℝ) ≤ Δ.coeff Q) :
    IsDltPair sX (n + 1) K (Finsupp.single P 1 + B) := by
  classical
  have hcoeff : ∀ Q, DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℚ) + B : QDivisor X) Q =
      (if P = Q then 1 else 0) + B Q :=
    fun Q => by rw [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.single_apply]
  show IsDltPair sX (n + 1) K (Finsupp.single P 1 + B)
  obtain ⟨X₀, hX₀s, hX₀snc, hX₀c⟩ :=
    MMP.Mori.exists_isSNC_restrictOpen_of_isNormalVariety sX hQ.1 (Finsupp.single P 1 + B)
  refine ⟨⟨hQ.1, hK, isQCartier_of_isQFactorial sX hQ _⟩, fun Q => ?_, X₀, hX₀s, hX₀snc,
    fun D a hD ha => ?_⟩
  · rw [hcoeff]
    split_ifs with h
    · subst h
      rw [← DivisorWithCoeffs.coeff_apply, hBP]
      norm_num
    · rw [zero_add]
      exact ⟨hB0 Q, (hB1 Q).le⟩
  · have hmem : D.f D.E.genericPoint ∉ X₀ := fun h =>
      hD D.isGenericPoint_center.mem h
    have h2 : 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
      by_contra hlt
      exact hmem (hX₀c _ (Order.le_of_lt_add_one (by
        rw [not_le] at hlt; exact_mod_cast hlt)))
    have hexc : D.IsExceptional :=
      (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight
        hQ.1 D).mpr h2
    refine neg_one_lt_of_isDiscrepancy hQ hplt (fun Q => ?_) D hexc a ha
    rw [hcoeff, DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.single_apply]
    have : ((B Q : ℚ) : ℝ) ≤ Δ Q := hBΔ Q
    split_ifs <;> push_cast <;> linarith

/-- **Rational sub-boundaries of a real plt pair are plt.** If every exceptional divisor over the
`ℚ`-factorial variety `X` of dimension `n + 1 ≥ 2` has positive log discrepancy for `S + Δ`, and
`0 ≤ B ≤ Δ` is a `ℚ`-divisor with coefficients `< 1` and no `S`-component, then `(X, S + B)` is
dlt, hence plt since its round down is `S`. -/
private theorem isPltPair_add_single (hQ : IsQFactorial sX) {P : Mori.PrimeDivisor X}
    {Δ : RDivisor X}
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) E a → 0 < a)
    {n : ℕ} (hn : 1 ≤ n) {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (B : QDivisor X) (hB0 : 0 ≤ B) (hBP : B.coeff P = 0) (hB1 : ∀ Q, B.coeff Q < 1)
    (hBΔ : ∀ Q, (B.coeff Q : ℝ) ≤ Δ.coeff Q) :
    IsPltPair sX (n + 1) K (Finsupp.single P 1 + B) := by
  classical
  have hcoeff : ∀ Q, DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℚ) + B : QDivisor X) Q =
      (if P = Q then 1 else 0) + B Q :=
    fun Q => by rw [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.single_apply]
  have hdlt := isDltPair_add_single hQ hplt hK B hB0 hBP hB1 hBΔ
  refine hdlt.isPltPair_of_pairwise_disjoint (by omega) (fun Q => ?_) ?_
  · have := hcoeff Q
    rw [DivisorWithCoeffs.coeff_apply] at this
    rw [Finsupp.coe_zero, Pi.zero_apply, this]
    exact add_nonneg (by split_ifs <;> norm_num) (hB0 Q)
  · refine (Set.subsingleton_singleton (a := P)).anti (fun Q hQ => ?_) |>.pairwise _
    by_contra hQP
    apply hQ
    rw [DivisorWithCoeffs.coeff_roundDown, hcoeff, if_neg (Ne.symm hQP), zero_add,
      Int.floor_eq_zero_iff]
    exact ⟨hB0 Q, hB1 Q⟩

end SubBoundary

/-! ### The coefficients of the real different -/

section Coefficients

variable {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
  [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
  (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
  [CompactSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))

/-- A `ℚ`-divisor on `T` whose `ℝ`-divisor is the pull-back of a `ℚ`-Cartier `C` is the
pull-back of `C`. -/
private theorem isPullback_of_isRCartierPullback {C : QDivisor X} (hCq : C.IsQCartier)
    (hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ C.supp)
    {C'' : QDivisor T}
    (h : MMP.Flips.IsRCartierPullback j (QDivisor.toRDivisor C) (QDivisor.toRDivisor C'')) :
    C.IsPullback j hgen C'' := by
  obtain ⟨C', hC', -⟩ := hCq.existsUnique_isPullback hgen
  have := isRCartierPullback_eq j (isRCartierPullback_of_isPullback j hCq hC') h
  rwa [QDivisor.toRDivisor_injective this] at hC'

omit [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] in
private theorem toRDivisor_smul (t : ℚ) (D : QDivisor X) :
    QDivisor.toRDivisor (t • D) = (t : ℝ) • QDivisor.toRDivisor D := by
  ext E
  change ((t * D E : ℚ) : ℝ) = (t : ℝ) * ((D E : ℚ) : ℝ)
  push_cast
  ring

include hP in
/-- **The coefficients of the real different** (FA 16.6, affinely extended). At a prime divisor
`Q'` of `S` there are `m ≥ 1` and `r_Q ∈ ℕ` with `coeff_{Q'} B_S⁰ = 1 - 1/m` and
`coeff_{Q'} (Q|_S) = r_Q / m` for every component `Q` of `Δ`: evaluate the rational formula
`coeff_{Q'} Diff_S(B) = 1 - 1/m + ∑ r_Q b_Q / m` at `B = 0` and at `B = t Q` for a small rational
`t ≤ δ_Q`, both plt. -/
private theorem exists_coeff_residueDifferent_eq (hX : IsNormalVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = n + 1) (hT : IsNormalVariety ℂ (j ≫ sX))
    (hQ : IsQFactorial sX) {Δ : RDivisor X} (hΔ : ∀ Q, 0 ≤ Δ.coeff Q ∧ Δ.coeff Q ≤ 1)
    (hΔP : Δ.coeff P = 0)
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) E a → 0 < a)
    (hn : 1 ≤ n) {R : Mori.PrimeDivisor X → QDivisor T}
    (hR : ∀ Q, Q ≠ P → R Q ≥ 0 ∧
      ∃ hgen : ∀ Z : irreducibleComponents T,
          j (componentGenericPoint T Z) ∉ DivisorWithCoeffs.supp (Finsupp.single Q (1 : ℚ) : QDivisor X),
        QDivisor.IsPullback j (Finsupp.single Q (1 : ℚ) : QDivisor X) hgen (R Q))
    {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0) (hτ₀ : P.ordForm τ₀ = -1)
    (hK₀ : (divisorOfForm τ₀).IsCanonicalDivisor sX (n + 1))
    {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀)
    {BS₀ : QDivisor T}
    (hBS₀ : ∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
        (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + 0 : QDivisor X).supp,
      (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + 0 : QDivisor X).IsPullback j
        hgen (Divisor.toQDivisor (divisorOfForm ρ₀) + BS₀))
    (Q' : Mori.PrimeDivisor T) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ r : Mori.PrimeDivisor X → ℕ, BS₀.coeff Q' = 1 - 1 / m ∧
      ∀ Q ∈ Δ.support, (R Q).coeff Q' = r Q / m := by
  classical
  have hQP : ∀ Q ∈ Δ.support, Q ≠ P := fun _ => ne_of_mem_support hΔP
  obtain ⟨m, hm, r, -, hall⟩ := MMP.Fourfold.coeff_residueDifferent_eq_of_isPltPair sX hX hdim j
    hT P hP τ₀ hτ₀0 hτ₀ ρ₀ hρ₀ Q' (fun i : Δ.support => (i : Mori.PrimeDivisor X))
    (fun i => hQP i i.2)
  -- the rational formula, for a sub-boundary `B` written as `∑ b_i Q_i`
  have key : ∀ (b : Δ.support → ℚ) (B : QDivisor X),
      ∑ i, b i • Finsupp.single (i : Mori.PrimeDivisor X) (1 : ℚ) = B → (∀ i, 0 ≤ b i) →
      0 ≤ B → B.coeff P = 0 → (∀ Q, B.coeff Q < 1) → (∀ Q, (B.coeff Q : ℝ) ≤ Δ.coeff Q) →
      ∀ BS : QDivisor T, MMP.Flips.IsRCartierPullback j
        (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + B))
        (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm ρ₀) + BS)) →
      BS.coeff Q' = 1 - 1 / m + ∑ i, (r i : ℚ) * b i / m := by
    intro b B hbB hb0 hB0 hBP hB1 hBΔ BS hBS
    subst hbB
    have hplt' := isPltPair_add_single hQ hplt hn hK₀ _ hB0 hBP hB1 hBΔ
    have hgen := map_componentGenericPoint_notMem_supp_divisorOfForm_add sX j P hP hτ₀ hBP
    exact (hall b hb0 (isQCartier_of_isQFactorial sX hQ _) hplt' BS
      ⟨hgen, isPullback_of_isRCartierPullback j (isQCartier_of_isQFactorial sX hQ _) hgen hBS⟩).1
  obtain ⟨hgen₀, hpb₀⟩ := hBS₀
  have h₀ := isRCartierPullback_of_isPullback j (isQCartier_of_isQFactorial sX hQ _) hpb₀
  -- `b = 0`
  have hBS₀c : BS₀.coeff Q' = 1 - 1 / m := by
    have := key 0 0 (by simp) (fun _ => le_rfl) le_rfl rfl (fun _ => zero_lt_one)
      (fun Q => by simpa using (hΔ Q).1) BS₀ h₀
    simpa using this
  refine ⟨m, hm, fun Q => if h : Q ∈ Δ.support then r ⟨Q, h⟩ else 0, hBS₀c, fun Q hQΔ => ?_⟩
  simp only [dif_pos hQΔ]
  -- `b = t Q` for a small rational `t`
  have hδ : 0 < Δ.coeff Q := lt_of_le_of_ne (hΔ Q).1 (Ne.symm (Finsupp.mem_support_iff.mp hQΔ))
  obtain ⟨t, ht0, ht⟩ := exists_rat_btwn (lt_min hδ (zero_lt_one' ℝ))
  have ht0' : (0 : ℚ) < t := by exact_mod_cast ht0
  have htδ : (t : ℝ) ≤ Δ.coeff Q := (ht.trans_le (min_le_left _ _)).le
  have ht1 : t < 1 := by exact_mod_cast ht.trans_le (min_le_right _ _)
  set i₀ : Δ.support := ⟨Q, hQΔ⟩
  have hsingle : ∀ G, DivisorWithCoeffs.coeff (t • Finsupp.single Q (1 : ℚ) : QDivisor X) G =
      if Q = G then t else 0 := fun G => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> simp
  have hsum : ∑ i, (Pi.single i₀ t : Δ.support → ℚ) i •
      Finsupp.single (i : Mori.PrimeDivisor X) (1 : ℚ) = t • Finsupp.single Q (1 : ℚ) := by
    rw [Fintype.sum_eq_single i₀ fun i hi => by rw [Pi.single_eq_of_ne hi, zero_smul],
      Pi.single_eq_same]
  have hpbQ : MMP.Flips.IsRCartierPullback j
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 +
        t • Finsupp.single Q (1 : ℚ)))
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm ρ₀) + (BS₀ + t • R Q))) := by
    obtain ⟨-, hg, hp⟩ := hR Q (hQP Q hQΔ)
    have h1 := MMP.Fourfold.isRCartierPullback_smul (t : ℝ)
      (isRCartierPullback_of_isPullback j (isQCartier_of_isQFactorial sX hQ _) hp)
    have h2 := MMP.Fourfold.isRCartierPullback_add h₀ h1
    convert h2 using 1
    · simp only [map_add, map_zero, add_zero, toRDivisor_smul]
    · simp only [map_add, toRDivisor_smul, add_assoc]
  have hval := key (Pi.single i₀ t) _ hsum (fun i => by
      by_cases hi : i = i₀
      · subst hi; simp [ht0'.le]
      · simp [Pi.single_eq_of_ne hi])
    (fun G => by
      change (0 : ℚ) ≤ DivisorWithCoeffs.coeff (t • Finsupp.single Q (1 : ℚ) : QDivisor X) G
      rw [hsingle]; split_ifs <;> linarith)
    (by rw [hsingle, if_neg (hQP Q hQΔ)])
    (fun G => by rw [hsingle]; split_ifs <;> linarith)
    (fun G => by
      rw [hsingle]
      split_ifs with h
      · subst h; exact htδ
      · simpa using (hΔ G).1)
    (BS₀ + t • R Q) hpbQ
  rw [Fintype.sum_eq_single i₀ fun i hi => by rw [Pi.single_eq_of_ne hi, mul_zero, zero_div],
    Pi.single_eq_same] at hval
  have hc : DivisorWithCoeffs.coeff (BS₀ + t • R Q) Q' = BS₀.coeff Q' + t * (R Q).coeff Q' := by
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  rw [hc, hBS₀c] at hval
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp at hval ⊢
  have : t * (m * (R Q).coeff Q') = t * r i₀ := by linear_combination hval
  exact mul_left_cancel₀ ht0'.ne' this

end Coefficients

/-! ### Rational klt adjunction -/

section RationalKlt

variable {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
  [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
  (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
  [CompactSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))

include hP in
/-- **Rational adjunction is klt.** Let `B ≥ 0` be a `ℚ`-divisor without `S`-component such that
every exceptional divisor over `X` has positive log discrepancy for `S + B`, and let `B_S` be its
residue different, `(div τ₀ + S + B)|_S = div ρ₀ + B_S`. Then every divisor over `S` has
positive log discrepancy for `B_S`: by forward adjunction its discrepancy is that of an
exceptional divisor over `X`. -/
private theorem pos_of_isLogDiscrepancy_residueDifferent (hX : IsNormalVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = n + 1) (hT : IsNormalVariety ℂ (j ≫ sX))
    (hdimT : topologicalKrullDim T = n) (hQ : IsQFactorial sX) {B : QDivisor X} (hB0 : 0 ≤ B)
    (hBP : B.coeff P = 0)
    (hpos : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (QDivisor.toRDivisor (Finsupp.single P 1 + B)) E a →
        0 < a)
    {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0) (hτ₀ : P.ordForm τ₀ = -1)
    (hK₀ : (divisorOfForm τ₀).IsCanonicalDivisor sX (n + 1))
    {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀)
    (hρ₀0 : ρ₀ ≠ 0) (hKρ₀ : (divisorOfForm ρ₀).IsCanonicalDivisor (j ≫ sX) n)
    {BS : QDivisor T}
    (hBS : MMP.Flips.IsRCartierPullback j
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + B))
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm ρ₀) + BS)))
    (m : ℕ) (F : DivisorOver ℂ (j ≫ sX)) (a : ℝ)
    (hF : MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m (QDivisor.toRDivisor BS) F a) :
    0 < a := by
  haveI : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hgen := map_componentGenericPoint_notMem_supp_divisorOfForm_add sX j P hP hτ₀ hBP
  have hCq := isQCartier_of_isQFactorial sX hQ
    (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + B)
  have hpb := isPullback_of_isRCartierPullback j hCq hgen hBS
  -- `(S, B_S)` is a pair
  obtain ⟨M₀, hM₀, DM, hDM, hDMc⟩ := hCq.exists_pos
  obtain ⟨DS, hDS, hDSp⟩ := hpb M₀ hM₀ DM hDM hDMc
  have hPairS : MMP.Mori.IsPair (j ≫ sX) BS :=
    ⟨hT, n, divisorOfForm ρ₀, hKρ₀, (M₀ : ℤ), by exact_mod_cast hM₀.ne',
      ⟨DS, hDS, hDSp.isCartier hDMc⟩⟩
  -- the index is the dimension
  have hm : m = n := by
    have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hF).symm.trans hdimT
    exact_mod_cast this
  rw [hm] at hF
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPairS hKρ₀ F
  have hac := ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc a).mp hF).2
  -- forward adjunction
  obtain ⟨M, rfl⟩ : ∃ M, M₀ = M + 1 := ⟨M₀ - 1, by omega⟩
  have hDM' : Divisor.toQDivisor DM = ((M + 1 : ℕ) : ℤ) •
      (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + B) := hDM
  have hgens := Aux.exists_generatesOn_isPoincareResidue sX hdim j hT hdimT P hP B τ₀ hτ₀0 ρ₀
    hρ₀ hρ₀0 BS hgen hpb M DM hDM' hDMc
  obtain ⟨E, hE, -, hiff⟩ := MMP.Fourfold.exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue
    sX hX n (divisorOfForm τ₀) hK₀ P j hT hP (divisorOfForm ρ₀) hKρ₀ B hB0 hBP
    ⟨M + 1, hM₀, by rw [← add_assoc]; exact ⟨DM, hDM, hDMc⟩⟩ BS ⟨M + 1, hM₀, hgens⟩ F
  have hEd := (hiff c).mp hc
  have hlt := neg_one_lt_of_isDiscrepancy_of_pos hX hpos E hE c hEd
  have : (-1 : ℝ) < (c : ℝ) := by exact_mod_cast hlt
  linarith

end RationalKlt

/-! ### Zero-dimensional centres -/

/-- A normal variety without prime divisors is a point, and has no divisors over it: a model
`Y` birational to it has dimension zero, so no point of coheight one. -/
private theorem false_of_isEmpty_primeDivisor {S : Scheme.{0}} {sS : S ⟶ Spec (.of ℂ)}
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] (hS : IsNormalVariety ℂ sS)
    (h : IsEmpty (Mori.PrimeDivisor S)) (D : DivisorOver ℂ sS) : False := by
  haveI := hS.1
  haveI := D.isNormalVariety.1
  haveI := D.isIntegral
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  have hdim := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS (D.f ≫ sS)
    D.isBirationalMorphism
  have hd := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg sS
  have hd0 : (letI := functionFieldAlgebra sS; (Algebra.trdeg ℂ S.functionField).toNat) = 0 := by
    by_contra hne
    exact h.false (MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hd hne).some
  have hY : topologicalKrullDim D.Y = ((0 : ℕ) : WithBot ℕ∞) := by
    rw [← hdim, hd, hd0]
  let _ : PartialOrder D.Y := specializationOrder D.Y
  have hk : Order.krullDim D.Y = ((0 : ℕ) : WithBot ℕ∞) := by
    rw [← hY]
    exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := D.Y))).symm
  have := Order.coheight_le_krullDim D.E.genericPoint
  rw [hk, D.E.coheight_genericPoint] at this
  exact absurd this (by decide)

/-! ### Effective pull-backs along arbitrary morphisms -/

section EffectivePullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem notMem_supp_sum_zsmul (f : Y ⟶ X) {m : ℕ} (n : Fin m → ℤ) {L : Fin m → Divisor X}
    (hB : ∀ j, ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (L j).supp)
    (s : Finset (Fin m)) :
    ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (∑ j ∈ s, n j • L j).supp := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro Z h
    rw [Finset.sum_empty, DivisorWithCoeffs.supp_zero] at h
    exact h
  | insert j s hj ih =>
    intro Z h
    rw [Finset.sum_insert hj] at h
    rcases DivisorWithCoeffs.supp_add_le _ _ h with h | h
    · obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
      rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hE
      exact hB j Z (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, right_ne_zero_of_mul hE, hmem⟩)
    · exact ih Z h

/-- `f^*(∑ nⱼ Lⱼ) = ∑ nⱼ f^*Lⱼ` for Cartier divisors `Lⱼ` which can be pulled back along `f`. -/
private theorem isPullback_sum_zsmul' [CompactSpace Y] (f : Y ⟶ X) {m : ℕ} (n : Fin m → ℤ)
    {L : Fin m → Divisor X} {L' : Fin m → Divisor Y} (hL : ∀ j, (L j).IsCartier)
    (hB : ∀ j, ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (L j).supp)
    (hp : ∀ j, (L j).IsPullback f (hB j) (L' j)) (s : Finset (Fin m)) :
    (∑ j ∈ s, n j • L j).IsPullback f (notMem_supp_sum_zsmul f n hB s) (∑ j ∈ s, n j • L' j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Divisor.isPullback_zero _
  | insert j s hj ih =>
    have key := Divisor.IsPullback.add ((hL j).zsmul _) (MMP.Fourfold.isCartier_sum_zsmul n hL s)
      (by have := notMem_supp_sum_zsmul f n hB (insert j s); rwa [Finset.sum_insert hj] at this)
      ((hp j).zsmul (hL j) (n j) (fun Z hZ => hB j Z (by
        obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
        rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hE
        exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, right_ne_zero_of_mul hE, hmem⟩))) ih
    convert key using 1 <;> simp only [Finset.sum_insert hj]

/-- **Effective `ℝ`-Cartier divisors pull back to effective divisors**, along any morphism from
a normal scheme for which the pull-back is defined: an effective `∑ rⱼ Lⱼ` is a nonnegative
combination of effective integral combinations of the `Lⱼ`, whose local equations are
regular. -/
private theorem coeff_nonneg_of_isRCartierPullback' [CompactSpace Y] (h : Y ⟶ X)
    {L : RDivisor X} {G : RDivisor Y} (hG : MMP.Flips.IsRCartierPullback h L G)
    (hL : ∀ P, 0 ≤ L.coeff P) (Γ : Mori.PrimeDivisor Y) : 0 ≤ G.coeff Γ := by
  classical
  obtain ⟨m, r, C, C', hC, hLeq, hp, rfl⟩ := hG
  choose hB hp' using hp
  rw [MMP.Flips.coeff_sum_smul_toRDivisor]
  have hcomm : ∑ j, r j * ((C' j).coeff Γ : ℝ) = ∑ j, ((C' j).coeff Γ : ℝ) * r j :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hcomm]
  refine MMP.Fourfold.sum_mul_nonneg_of_forall_int (ι := Mori.PrimeDivisor X)
    (fun P j => (C j).coeff P) (fun j => (C' j).coeff Γ) r ?_ ?_ ?_
  · have hfS : (⋃ j : Fin m, ((C j).support : Set (Mori.PrimeDivisor X))).Finite :=
      Set.finite_iUnion fun j => (C j).support.finite_toSet
    refine hfS.subset fun P hP => ?_
    obtain ⟨j, hj⟩ : ∃ j, (C j).coeff P ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hP (funext hcon)
    exact Set.mem_iUnion.2 ⟨j, Finsupp.mem_support_iff.mpr hj⟩
  · intro nn hn
    have hBV : ∀ P : Mori.PrimeDivisor X, (P.support ∩ (⊤ : X.Opens)).Nonempty →
        0 ≤ (∑ j, nn j • C j).coeff P := fun P _ => by
      rw [MMP.Fourfold.coeff_sum_zsmul]
      simpa [mul_comm] using hn P
    have := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn
      (MMP.Fourfold.isCartier_sum_zsmul nn hC Finset.univ) hBV
      (isPullback_sum_zsmul' h nn hC hB hp' Finset.univ) Γ
      ⟨Γ.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support Γ, trivial⟩
    rw [MMP.Fourfold.coeff_sum_zsmul] at this
    simpa [mul_comm] using this
  · intro P
    have := hL P
    rw [hLeq, MMP.Flips.coeff_sum_smul_toRDivisor] at this
    simpa [mul_comm] using this

end EffectivePullback

/-! ### Openness of plt and convexity of klt -/

section KltRegion

/-- Finitely many strict inequalities `0 < ℓ s` and `0 < ℓ s + ℓ t` between continuous functions
which hold at `x` persist near `x`. -/
theorem eventually_pos_of_continuous {E σ : Type*} [TopologicalSpace E] {S : Finset σ}
    {exc : σ → Prop} {meet : σ → σ → Prop} {ℓ : σ → E → ℝ} (hcont : ∀ s, Continuous (ℓ s))
    {x : E} (hexc : ∀ s ∈ S, exc s → 0 < ℓ s x)
    (hmeet : ∀ s ∈ S, ∀ t ∈ S, meet s t → 0 < ℓ s x + ℓ t x) :
    ∀ᶠ y in nhds x, (∀ s ∈ S, exc s → 0 < ℓ s y) ∧
      ∀ s ∈ S, ∀ t ∈ S, meet s t → 0 < ℓ s y + ℓ t y := by
  refine ((Filter.eventually_all_finset S).2 fun s hs => ?_).and
    ((Filter.eventually_all_finset S).2 fun s hs => (Filter.eventually_all_finset S).2
      fun t ht => ?_)
  · by_cases he : exc s
    · filter_upwards [((hcont s).tendsto x).eventually (lt_mem_nhds (hexc s hs he))]
        with y hy _ using hy
    · exact Filter.Eventually.of_forall fun y h => absurd h he
  · by_cases hst : meet s t
    · filter_upwards [(((hcont s).add (hcont t)).tendsto x).eventually
        (lt_mem_nhds (hmeet s hs t ht hst))] with y hy _ using hy
    · exact Filter.Eventually.of_forall fun y h => absurd h hst

/-- A sum of single-coefficient divisors along distinct prime divisors, each with coefficient at
most `1`, has every coefficient at most `1`. -/
theorem coeff_sum_single_le_one {X : Scheme.{0}} {κ : Type*} [Fintype κ]
    {p : κ → Mori.PrimeDivisor X} (hp : Function.Injective p) {y : κ → ℝ} (hy : ∀ o, y o ≤ 1)
    (Q : Mori.PrimeDivisor X) : (∑ o, Finsupp.single (p o) (y o) : RDivisor X).coeff Q ≤ 1 := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  by_cases hQo : ∃ o, p o = Q
  · obtain ⟨o, rfl⟩ := hQo
    rw [Fintype.sum_eq_single o fun o' ho' => Finsupp.single_eq_of_ne
      (fun e => ho' (hp e).symm), Finsupp.single_eq_same]
    exact hy o
  · rw [Fintype.sum_eq_zero _ fun o => Finsupp.single_eq_of_ne fun e => hQo ⟨o, e.symm⟩]
    norm_num

/-- **Plt is open in the coefficients.** On a `ℚ`-factorial variety, if every exceptional divisor
has positive log discrepancy for `S + ∑ xᵢ pᵢ` with all `xᵢ < 1`, the same holds for the rational
vectors `q` near `x`. -/
private theorem exists_nhds_pos_isLogDiscrepancy {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] (hQ : IsQFactorial sX) {ι : Type}
    [Fintype ι] (p : ι → Mori.PrimeDivisor X) (hp : Function.Injective p)
    (P : Mori.PrimeDivisor X) (hpP : ∀ i, p i ≠ P) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (x : ι → ℝ) (hx1 : ∀ i, x i < 1)
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m
        (Finsupp.single P 1 + ∑ i, Finsupp.single (p i) (x i)) E a → 0 < a) :
    ∃ U ∈ nhds x, ∀ q : ι → ℚ, (fun i => (q i : ℝ)) ∈ U →
      ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX m
          (Finsupp.single P 1 + ∑ i, Finsupp.single (p i) ((q i : ℝ))) E a → 0 < a := by
  classical
  let p' : Option ι → Mori.PrimeDivisor X := fun o => o.elim P p
  have hp' : Function.Injective p' := by
    rintro (_ | i) (_ | i') h
    · rfl
    · exact absurd h.symm (hpP i')
    · exact absurd h (hpP i)
    · exact congrArg some (hp h)
  let ext : (ι → ℝ) → Option ι → ℝ := fun y o => o.elim 1 y
  have hsum : ∀ y : ι → ℝ, (∑ o, Finsupp.single (p' o) (ext y o) : RDivisor X) =
      Finsupp.single P 1 + ∑ i, Finsupp.single (p i) (y i) := fun y => by
    rw [Fintype.sum_option]
    rfl
  obtain ⟨σ, S, c, w, exc, meet, ha, hb, hc, -, -, hpl⟩ := MMP.Fourfold.exists_resolution_data hQ p' hK
  let ℓ : σ → (ι → ℝ) → ℝ := fun s y => c s - ∑ o, ext y o * w s o
  have hcont : ∀ s, Continuous (ℓ s) := fun s =>
    continuous_const.sub (continuous_finset_sum _ fun o _ => by
      rcases o with _ | i
      · show Continuous fun _ : ι → ℝ => (1 : ℝ) * w s none
        exact continuous_const
      · exact (continuous_apply i).mul continuous_const)
  have hexc : ∀ s ∈ S, exc s → 0 < ℓ s x := fun s hs he => by
    obtain ⟨D, hD, hDa⟩ := ha s hs (ext x)
    exact hplt _ D _ (hD he) (by rwa [hsum] at hDa)
  have hmeet : ∀ s ∈ S, ∀ t ∈ S, meet s t → 0 < ℓ s x + ℓ t x := fun s hs t ht hst => by
    obtain ⟨D, hD, hDa⟩ := hb s hs t ht hst
    exact hplt _ D _ hD (by simpa only [hsum] using hDa (ext x))
  refine ⟨_, (eventually_pos_of_continuous hcont hexc hmeet).and
    (Filter.eventually_all.2 fun i => ((continuous_apply i).tendsto x).eventually
      (gt_mem_nhds (hx1 i))), fun q hq m E a hE ha' => ?_⟩
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hq
  let q' : Option ι → ℚ := fun o => o.elim 1 q
  have hq' : (fun o => ((q' o : ℚ) : ℝ)) = ext (fun i => (q i : ℝ)) := by
    funext o
    rcases o with _ | i <;> simp [q', ext]
  have hℓ : ∀ s, c s - ∑ o, ((q' o : ℚ) : ℝ) * w s o = ℓ s (fun i => (q i : ℝ)) := fun s => by
    simp only [ℓ, ← hq']
  refine hpl q' (fun s hs => ?_) (fun s hs he => hℓ s ▸ hq1 s hs he)
    (fun s hs t ht hst => hℓ s ▸ hℓ t ▸ hq2 s hs t ht hst) m E a hE ?_
  · by_cases he : exc s
    · exact hℓ s ▸ (hq1 s hs he).le
    · obtain ⟨Q, hQc⟩ := hc s hs he
      rw [hQc, sub_nonneg]
      refine coeff_sum_single_le_one hp' (fun o => ?_) Q
      rcases o with _ | i
      · simp [q']
      · simpa [q'] using (hq3 i).le
  · have h' := hsum (fun i => (q i : ℝ))
    simp only [← hq'] at h'
    rwa [h']

/-- **The klt region along `ℚ`-Cartier directions is convex**: with `mᵢ Rᵢ = Cᵢ` Cartier, it is
the preimage of the convex klt region along the `Cᵢ` under `y ↦ (yᵢ / mᵢ)ᵢ`. -/
private theorem convex_setOf_pos_isLogDiscrepancy_add {S : Scheme.{0}} (sS : S ⟶ Spec (.of ℂ))
    [IsIntegral S] [IsNormal S] [IsLocallyNoetherian S] (B₀ : RDivisor S) {ι : Type}
    [Fintype ι] (R : ι → QDivisor S) (hR : ∀ i, (R i).IsQCartier) :
    Convex ℝ {y : ι → ℝ | ∀ (m : ℕ) (F : DivisorOver ℂ sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS m (B₀ + ∑ i, y i • QDivisor.toRDivisor (R i)) F a →
        0 < a} := by
  classical
  choose m hm hCD using fun i => (hR i).exists_pos
  choose C hC hCc using hCD
  have hconv := MMP.Fourfold.convex_setOf_lt_isLogDiscrepancy_add (sX := sS) B₀ C hCc 0
    (fun _ => True)
  let L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := LinearMap.pi fun i => (1 / (m i : ℝ)) • LinearMap.proj i
  have hpre := hconv.linear_preimage L
  have hdiv : ∀ y : ι → ℝ, (∑ i, y i • QDivisor.toRDivisor (R i) : RDivisor S) =
      ∑ i, L y i • Divisor.toRDivisor (C i) := fun y => by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm0 : (m i : ℝ) ≠ 0 := by exact_mod_cast (hm i).ne'
    ext G
    have h := congrArg (fun D : QDivisor S => D.coeff G) (hC i)
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h
    simp only [L, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
      DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply]
    change y i * ((R i G : ℚ) : ℝ) = 1 / (m i : ℝ) * y i * ((C i G : ℤ) : ℝ)
    rw [show ((C i G : ℤ) : ℝ) = ((C i G : ℤ) : ℚ) by push_cast; rfl]
    rw [show ((C i G : ℤ) : ℚ) = (m i : ℚ) * R i G from h]
    push_cast
    field_simp
  refine (congrArg (Convex ℝ) ?_).mpr hpre
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, hdiv]
  exact ⟨fun h n D a _ ha => h n D a ha, fun h n D a ha => h n D a trivial ha⟩

end KltRegion

/-! ### Monotonicity along nonpositive diagrams -/

section Monotonicity

/-- **The strict transform of `S` is birational to `S`.** If `p : W ⟶ X` is an isomorphism of
local rings at the generic point of `T_W ⊆ W`, and `p_T : T_W ⟶ T` is the restriction of `p` to
integral closed subschemes, then `p_T^* : k(T) → k(T_W)` is bijective. -/
private theorem functionFieldMap_bijective_of_comp_eq {X W T TW : Scheme.{0}} [IsIntegral T]
    [IsIntegral TW] (p : W ⟶ X) (j : T ⟶ X) (jW : TW ⟶ W) [IsClosedImmersion jW]
    (pT : TW ⟶ T) [IsDominant pT] (hpT : pT ≫ j = jW ≫ p)
    [IsIso (p.stalkMap (jW (genericPoint TW)))] :
    Function.Bijective (functionFieldMap pT) := by
  refine ⟨(functionFieldMap pT).injective, fun y => ?_⟩
  obtain ⟨b, hb⟩ := SurjectiveOnStalks.stalkMap_surjective jW (genericPoint TW) y
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (p.stalkMap (jW (genericPoint TW)))).2 b
  have key : ∀ c : X.presheaf.stalk ((jW ≫ p) (genericPoint TW)),
      ∃ a : T.presheaf.stalk (pT (genericPoint TW)),
        (pT.stalkMap (genericPoint TW)).hom a = ((jW ≫ p).stalkMap (genericPoint TW)).hom c := by
    rw [← hpT]
    intro c
    exact ⟨(j.stalkMap (pT (genericPoint TW))).hom c, by rw [Scheme.Hom.stalkMap_comp]; rfl⟩
  obtain ⟨a, ha⟩ := key c
  refine ⟨algebraMap _ T.functionField a, ?_⟩
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk, ha, Scheme.Hom.stalkMap_comp]
  rw [MMP.CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint]
  exact hb

/-! ### Changing the structure morphism of forms -/

section Cast

variable {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]

/-- The order of a form does not see a change of the structure morphism. -/
private theorem ordForm_cast [IsLocallyNoetherian Y] {s₁ s₂ : Y ⟶ Spec (.of k)} (h : s₁ = s₂)
    {d : ℕ} {m : ℤ} (ρ : RationalPluriForms s₁ d m) (E : Mori.PrimeDivisor Y) :
    E.ordForm (cast (congrArg (fun s => RationalPluriForms s d m) h) ρ) = E.ordForm ρ := by
  subst h; rfl

/-- Pull-back of forms commutes with a change of the structure morphism. -/
private theorem pullbackRationalPluriForms_cast {Z : Scheme.{0}} [IsIntegral Z] (f : Z ⟶ Y)
    [IsDominant f] {s₁ s₂ : Y ⟶ Spec (.of k)} (h : s₁ = s₂) {d : ℕ} {m : ℤ}
    (ρ : RationalPluriForms s₁ d m) :
    pullbackRationalPluriForms s₂ f (cast (congrArg (fun s => RationalPluriForms s d m) h) ρ) =
      cast (congrArg (fun s => RationalPluriForms (f ≫ s) d m) h)
        (pullbackRationalPluriForms s₁ f ρ) := by
  subst h; rfl

/-- Poincaré residues do not see a change of the structure morphism. -/
private theorem isPoincareResidue_cast [IsLocallyNoetherian Y] {T : Scheme.{0}} [IsIntegral T] {s₁ s₂ : Y ⟶ Spec (.of k)}
    (h : s₁ = s₂) (j : T ⟶ Y) {n m : ℕ} {τ : RationalPluriForms s₁ (n + 1) m}
    {ρ : RationalPluriForms (j ≫ s₁) n m} (hr : IsPoincareResidue s₁ j n m τ ρ) :
    IsPoincareResidue s₂ j n m (cast (congrArg (fun s => RationalPluriForms s (n + 1) m) h) τ)
      (cast (congrArg (fun s => RationalPluriForms (j ≫ s) n m) h) ρ) := by
  subst h; exact hr

end Cast

/-- The restriction `p_T : T_W ⟶ T` of a proper morphism to integral closed subschemes, which is
a local isomorphism at the generic point of `T_W`, is birational. -/
private theorem isBirationalMorphism_of_comp_eq {X W T TW : Scheme.{0}} [IsIntegral T]
    [IsIntegral TW] (p : W ⟶ X) [IsProper p] (j : T ⟶ X) [IsClosedImmersion j] (jW : TW ⟶ W)
    [IsClosedImmersion jW] (pT : TW ⟶ T) [IsDominant pT] (hpT : pT ≫ j = jW ≫ p)
    [IsIso (p.stalkMap (jW (genericPoint TW)))] : IsBirationalMorphism pT := by
  haveI : IsProper (pT ≫ j) := hpT ▸ inferInstance
  haveI : IsProper pT := IsProper.of_comp pT j
  exact MMP.Mori.isBirationalMorphism_of_bijective_functionFieldMap pT
    (functionFieldMap_bijective_of_comp_eq p j jW pT hpT)

/-! ### Cartier divisors along the strict transform -/

section StrictTransform

variable {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
  [IsLocallyNoetherian W] [IsNormal W]

/-- Pull-backs of a Cartier divisor along equal morphisms agree. -/
private theorem isPullback_eq_of_eq [CompactSpace W] {f₁ f₂ : W ⟶ X} (hf : f₁ = f₂) {C : Divisor X}
    (hC : C.IsCartier) {hB₁ : ∀ Z : irreducibleComponents W, f₁ (componentGenericPoint W Z) ∉ C.supp}
    {hB₂ : ∀ Z : irreducibleComponents W, f₂ (componentGenericPoint W Z) ∉ C.supp}
    {C₁ C₂ : Divisor W} (h₁ : C.IsPullback f₁ hB₁ C₁) (h₂ : C.IsPullback f₂ hB₂ C₂) : C₁ = C₂ := by
  subst hf
  exact (Divisor.IsPullback.pullback_eq hC h₁).symm.trans (Divisor.IsPullback.pullback_eq hC h₂)

/-- If `p : W ⟶ X` maps the generic point of a prime divisor `P_W` to that of `P` and is a local
isomorphism there, the pull-back of a Cartier divisor `C` not containing `P` does not contain
`P_W`. -/
private theorem genericPoint_notMem_supp_of_isPullback (p : W ⟶ X) [IsDominant p]
    (P : Mori.PrimeDivisor X) (PW : Mori.PrimeDivisor W) (hpPW : p PW.genericPoint = P.genericPoint)
    [IsIso (p.stalkMap PW.genericPoint)] {C : Divisor X} (hC : C.IsCartier) (hCP : C.coeff P = 0)
    {hB : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ C.supp}
    {C' : Divisor W} (h : C.IsPullback p hB C') : PW.genericPoint ∉ C'.supp := by
  intro hm
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hm
  obtain rfl := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E PW hmem
  apply hE
  obtain ⟨U, hU, φ, hφ⟩ := hC P.genericPoint
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ E (hpPW ▸ hU)
    (MMP.Mori.pointComponent P.genericPoint), MMP.Positivity.ord_functionFieldMap_of_isIso p E P hpPW]
  have h2 := hφ P ((P.genericPoint_mem_iff U).mp hU)
  rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h2
  have hZ : P.component = MMP.Mori.pointComponent P.genericPoint := Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  rw [hZ, hCP] at h2
  exact_mod_cast h2.symm

end StrictTransform

/-- **The log discrepancy on another model.** A log discrepancy of `(T, B)` along `D` is computed,
with any top form `ω` and any presentation of `K_T + B` by Cartier divisors, on every model `D₁` of
the same valuation, proper or not. -/
private theorem isLogDiscrepancy_eq_of_valuation_eq {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T]
    {d m : ℕ} {B : RDivisor T} {D : DivisorOver ℂ sT} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sT m B D a)
    {ω : RationalPluriForms sT d 1} (hω0 : ω ≠ 0)
    (hK : ∃ K : Divisor T, K.IsCanonicalDivisor sT d ∧ ∀ Γ, K.coeff Γ = Γ.ordForm ω)
    {k : ℕ} (r : Fin k → ℝ) (C : Fin k → Divisor T) (hC : ∀ i, (C i).IsCartier)
    (hsum : ∀ Γ : Mori.PrimeDivisor T, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ)
    (D₁ : DivisorOver ℂ sT) (hv : D₁.valuation = D.valuation) (C₁ : Fin k → Divisor D₁.Y)
    (hC₁ : haveI := D₁.isLocallyNoetherian; haveI := D₁.isNormal
      ∀ i, ∃ h, (C i).IsPullback D₁.f h (C₁ i)) :
    a = 1 + D₁.ordPullback ω - ∑ i, r i * (C₁ i).coeff D₁.E := by
  obtain ⟨hT, hprop, -⟩ := id ha
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := D₁.isIntegral
  haveI := D₁.isLocallyNoetherian
  haveI := D₁.isNormal
  haveI := D₁.isDominant
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hC i)
  have hb : MMP.Intersection.IsLogDiscrepancy sT d B D
      (1 + D.ordPullback ω - ∑ i, r i * (C' i).coeff D.E) :=
    ⟨hT, hprop, ω, hω0, hK, k, r, C, C', hC, hsum, fun i => ⟨_, hC' i⟩, rfl⟩
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha hb]
  obtain ⟨K, hKc, -⟩ := hK
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hT
    hKc.topologicalKrullDim_eq hv.symm ω]
  have hcen := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hT hv
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  obtain ⟨h₁, hp₁⟩ := hC₁ i
  obtain ⟨U, hU, φ, hφ⟩ := hC i (D.f D.E.genericPoint)
  let Z := MMP.Mori.pointComponent (D.f D.E.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hC' i) hφ D.E hU Z,
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hp₁ hφ D₁.E (hcen ▸ hU) Z]
  have hne : MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions T) ≠ 0 :=
    ((φ.isUnit.map _).ne_zero)
  exact MMP.Threefold.Bridges.ord_functionFieldMap_eq_of_valuationOver_eq D₁.E D.E hv hne

/-- **One side of a nonpositive diagram.** Let `p : W ⟶ X` be proper birational, `P_W ⊆ W` a prime
divisor over `S = P` with closed subscheme `T_W` and `p_T : T_W ⟶ T`, and `τ_W` a top form on `W`
with a simple pole along `P_W` and residue `ρ_W`. Then `K_X + S + Δ` has a presentation whose
pull-back to `W` is a combination `∑ rᵢ Cᵢ` of Cartier divisors not containing `P_W`, computing the
log discrepancies over `X` of the prime divisors of `W` with the form `τ_W`, and computing on the
model of any divisor `G` over `T_W` the log discrepancy of `(T, Δ_S)` along `G` with the form
`ρ_W`. -/
private theorem exists_side_data
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (P : Mori.PrimeDivisor X) (Δ : RDivisor X)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    [IsNormal T] (hj : Set.range j.base = (P.support : Set X))
    (ΔS : RDivisor T)
    (hΔS : ∀ τ : RationalPluriForms sX (n + 1) 1, τ ≠ 0 → P.ordForm τ = -1 →
        ∀ ρ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 τ ρ →
          MMP.Flips.IsRCartierPullback j
            (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P 1 + Δ)
            (Divisor.toRDivisor (divisorOfForm ρ) + ΔS))
    {W TW : Scheme.{0}} (p : W ⟶ X) [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsDominant p] [IsProper p] (hpb : IsBirationalMorphism p)
    (sW : W ⟶ Spec (.of ℂ)) (hsW : p ≫ sX = sW)
    (PW : Mori.PrimeDivisor W) (hpPW : p PW.genericPoint = P.genericPoint)
    (jW : TW ⟶ W) [IsClosedImmersion jW] [IsIntegral TW]
    (hjW : Set.range jW.base = (PW.support : Set W))
    (pT : TW ⟶ T) [IsDominant pT] (hpT : pT ≫ j = jW ≫ p)
    (τW : RationalPluriForms sW (n + 1) 1) (hτW : PW.ordForm τW = -1)
    (ρW : RationalPluriForms (jW ≫ sW) n 1) (hρW : IsPoincareResidue sW jW n 1 τW ρW)
    (G : DivisorOver ℂ (jW ≫ sW)) (D : DivisorOver ℂ (j ≫ sX))
    (hD : D.valuation = G.valuation.comap (functionFieldMap pT))
    (m : ℕ) (a : ℝ) (ha : MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m ΔS D a) :
    ∃ (k : ℕ) (r : Fin k → ℝ) (C : Fin k → Divisor W), (∀ i, (C i).IsCartier) ∧
      (∀ i, PW.genericPoint ∉ (C i).supp) ∧
      (∀ E : Mori.PrimeDivisor W, ∃ DW : DivisorOver ℂ sX, DW.valuation = E.valuationOver p ∧
        MMP.Intersection.IsLogDiscrepancy sX (n + 1) (Finsupp.single P 1 + Δ) DW
          (1 + E.ordForm τW - ∑ i, r i * (C i).coeff E)) ∧
      haveI := G.isLocallyNoetherian
      haveI := G.isNormal
      ∃ (C' : Fin k → Divisor G.Y), (∀ i, ∃ h, (C i).IsPullback (G.f ≫ jW) h (C' i)) ∧
        a = 1 + G.ordPullback ρW - ∑ i, r i * (C' i).coeff G.E := by
  classical
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace p
  have hWv : IsNormalVariety ℂ (p ≫ sX) := by
    haveI := hX.1
    exact ⟨⟨⟩, inferInstance⟩
  haveI : LocallyOfFiniteType sW := hsW ▸ hWv.1.toLocallyOfFiniteType
  have hTv : IsNormalVariety ℂ (j ≫ sX) := by
    haveI := hX.1
    exact ⟨⟨⟩, inferInstance⟩
  haveI : LocallyOfFiniteType (j ≫ sX) := hTv.1.toLocallyOfFiniteType
  have hjT := Aux.map_genericPoint_eq j P hj
  have hjWT := Aux.map_genericPoint_eq jW PW hjW
  haveI : IsIso (p.stalkMap PW.genericPoint) :=
    MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb hpPW
  haveI : IsIso (p.stalkMap (jW (genericPoint TW))) :=
    MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb (by rw [hjWT, hpPW])
  have hpTbij := functionFieldMap_bijective_of_comp_eq p j jW pT hpT
  have hpTb := isBirationalMorphism_of_comp_eq p j jW pT hpT
  have hpbij := hpb.functionFieldMap_bijective
  have hd : (letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat) = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (letI := functionFieldAlgebra (j ≫ sX);
      (Algebra.trdeg ℂ T.functionField).toNat) = n := by
    have := Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  have hdimT : topologicalKrullDim T = n := by
    rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (j ≫ sX), hdT]
  -- the form `τ` on `X` with `p^*τ = τ_W`
  obtain ⟨τ, hτp⟩ := MMP.Mori.exists_pullbackRationalPluriForms_eq (sZ := sX) p hpbij hd
    (cast (congrArg (fun s => RationalPluriForms s (n + 1) (1 : ℤ)) hsW.symm) τW)
  have hτ : P.ordForm τ = -1 := by
    rw [← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hpbij hd PW P hpPW τ, hτp,
      ordForm_cast hsW.symm, hτW]
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [PrimeDivisor.ordForm_zero] at hτ
    norm_num at hτ
  -- its residue `ρ` along `T`
  have hT0 : Nonempty (Mori.PrimeDivisor T) := by
    by_contra h
    exact false_of_isEmpty_primeDivisor hTv (not_nonempty_iff.mp h) D
  obtain ⟨σ, hσ0, hσ, ρσ, hρσ, -⟩ :=
    MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue sX hX hdim j hTv P hj hT0.some
  obtain ⟨b, -, hρ⟩ := MMP.Fourfold.IsPoincareResidue.exists_unit_smul hdim P hjT hσ0 hτ0
    (hσ.trans hτ.symm) hρσ
  set ρ := (j.stalkMap (genericPoint T)).hom ((b⁻¹ : (X.presheaf.stalk _)ˣ) : _) • ρσ with hρdef
  have hρ0 : ρ ≠ 0 := Aux.isPoincareResidue_ne_zero sX hX hdim j hTv P hj τ hτ0 hτ ρ hρ hT0.some
  -- canonical divisors
  have hKρ := isCanonicalDivisor_divisorOfForm hTv hdimT hρ0
  have hKτ := isCanonicalDivisor_divisorOfForm hX (n := n + 1) (by rw [hdim]; norm_cast) hτ0
  -- a presentation of `K_X + S + Δ` restricting to `K_S + Δ_S`
  obtain ⟨k, r, C, CT, hC, hL, hCT, hG⟩ := hΔS τ hτ0 hτ ρ hρ
  have hCTc : ∀ i, (CT i).IsCartier := fun i => (hCT i).2.isCartier (hC i)
  have hCP : ∀ i, (C i).coeff P = 0 := fun i => by
    obtain ⟨hB, -⟩ := hCT i
    by_contra hne
    refine hB (MMP.Mori.pointComponent (genericPoint T))
      (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hne, ?_⟩)
    rw [componentGenericPoint_eq_genericPoint, hjT]
    exact MMP.Flips.primeDivisor_genericPoint_mem_support P
  choose CW hCW using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant p (hC i)
  have hCWc : ∀ i, (CW i).IsCartier := fun i => (hCW i).isCartier (hC i)
  have hCWP : ∀ i, PW.genericPoint ∉ (CW i).supp := fun i =>
    genericPoint_notMem_supp_of_isPullback p P PW hpPW (hC i) (hCP i) (hCW i)
  have hsumX : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm τ : ℝ) +
      (Finsupp.single P 1 + Δ : RDivisor X).coeff Γ = ∑ i, r i * ((C i).coeff Γ : ℝ) := by
    intro Γ
    have := congrArg (fun D : RDivisor X => D.coeff Γ) hL
    simp only [MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this]
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm]
    ring
  have hsumT : ∀ Γ : Mori.PrimeDivisor T, (Γ.ordForm ρ : ℝ) + ΔS.coeff Γ =
      ∑ i, r i * ((CT i).coeff Γ : ℝ) := by
    intro Γ
    have := congrArg (fun D : RDivisor T => D.coeff Γ) hG
    simp only [MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm]
  refine ⟨k, r, CW, hCWc, hCWP, fun E => ⟨⟨W, p, hWv, hpb, E⟩, rfl, ?_⟩, ?_⟩
  · -- the log discrepancy over `X` of a prime divisor of `W`
    have hb : MMP.Intersection.IsLogDiscrepancy sX (n + 1) (Finsupp.single P 1 + Δ)
        ⟨W, p, hWv, hpb, E⟩ (1 + (DivisorOver.ordPullback ⟨W, p, hWv, hpb, E⟩ τ : ℝ) -
          ∑ i, r i * ((CW i).coeff E : ℝ)) :=
      ⟨hX, inferInstance, τ, hτ0, ⟨divisorOfForm τ, hKτ, fun Γ => rfl⟩, k, r, C, CW, hC, hsumX,
        fun i => ⟨_, hCW i⟩, rfl⟩
    have hord : (DivisorOver.ordPullback ⟨W, p, hWv, hpb, E⟩ τ : ℤ) = E.ordForm τW := by
      change E.ordForm (pullbackRationalPluriForms sX p τ) = _
      rw [hτp, ordForm_cast hsW.symm]
    rwa [hord] at hb
  · -- the log discrepancy over `S`, on the model of `G`
    haveI := G.isIntegral
    haveI := G.isNormal
    haveI := G.isLocallyNoetherian
    haveI := G.isDominant
    haveI : QuasiCompact (G.f ≫ jW ≫ sW) := G.isNormalVariety.1.toQuasiCompact
    haveI : CompactSpace G.Y := QuasiCompact.compactSpace_of_compactSpace (G.f ≫ jW ≫ sW)
    have hTW : pT ≫ j ≫ sX = jW ≫ sW := by rw [← hsW, reassoc_of% hpT]
    have hcomp : (G.f ≫ pT) ≫ j ≫ sX = G.f ≫ jW ≫ sW := by rw [Category.assoc, hTW]
    let GT : DivisorOver ℂ (j ≫ sX) :=
      ⟨G.Y, G.f ≫ pT, hcomp ▸ G.isNormalVariety,
        MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp G.isBirationalMorphism hpTb, G.E⟩
    have hGT : GT.valuation = D.valuation := by
      rw [hD]
      refine Valuation.ext fun t => ?_
      change G.E.divisorialValuation (functionFieldMap (G.f ≫ pT) t) =
        G.E.divisorialValuation (functionFieldMap G.f (functionFieldMap pT t))
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    choose C₁ hC₁ using fun i =>
      MMP.Threefold.Bridges.exists_isPullback_of_isDominant (G.f ≫ pT) (hCTc i)
    have ha1 := isLogDiscrepancy_eq_of_valuation_eq ha hρ0 ⟨divisorOfForm ρ, hKρ, fun Γ => rfl⟩ r
      CT hCTc hsumT GT hGT C₁ (fun i => ⟨_, hC₁ i⟩)
    -- the pull-backs of the `C_i` to the model of `G`
    have hgen : ∀ i, ∀ Z : irreducibleComponents G.Y,
        (G.f ≫ jW) (componentGenericPoint G.Y Z) ∉ (CW i).supp := fun i Z => by
      rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply,
        map_genericPoint_of_isDominant, hjWT]
      exact hCWP i
    choose C₂ hC₂ using fun i => (hCWc i).exists_isPullback (hgen i)
    have hC₁₂ : ∀ i, C₁ i = C₂ i := fun i => by
      obtain ⟨hB, hpbT⟩ := hCT i
      have hPnot : P.genericPoint ∉ (C i).supp := by
        have := hB (MMP.Mori.pointComponent (genericPoint T))
        rwa [componentGenericPoint_eq_genericPoint, hjT] at this
      have h1 := MMP.ProgramBaseChange.divisor_isPullback_comp (e := (G.f ≫ pT) ≫ j) rfl hpbT (hC₁ i) (fun Z => by
          rw [componentGenericPoint_eq_genericPoint]
          show j (pT (G.f (genericPoint G.Y))) ∉ _
          rw [map_genericPoint_of_isDominant G.f, map_genericPoint_of_isDominant pT, hjT]
          exact hPnot)
      have h2 := MMP.ProgramBaseChange.divisor_isPullback_comp (e := (G.f ≫ jW) ≫ p) rfl (hCW i) (hC₂ i) (fun Z => by
          rw [componentGenericPoint_eq_genericPoint]
          show p (jW (G.f (genericPoint G.Y))) ∉ _
          rw [map_genericPoint_of_isDominant G.f, hjWT, hpPW]
          exact hPnot)
      exact isPullback_eq_of_eq (by simp only [Category.assoc, hpT]) (hC i) h1 h2
    refine ⟨C₂, fun i => ⟨_, hC₂ i⟩, ?_⟩
    rw [ha1]
    simp only [hC₁₂]
    congr 2
    -- the order of the pulled-back residue: `ρ_W = p_T^*ρ`
    have hres := MMP.Fourfold.isPoincareResidue_pullback p j jW pT sX hpbij hpTbij hpT P hjT PW
      hjWT hd hdT hρ
    have hres' := isPoincareResidue_cast hsW jW hres
    rw [hτp] at hres'
    simp only [cast_cast, cast_eq] at hres'
    have huniq := MMP.Fourfold.IsPoincareResidue.unique_of_isClosedImmersion PW hjWT hρW hres'
    haveI : LocallyOfFiniteType (pT ≫ j ≫ sX) := hTW ▸ inferInstance
    have key : GT.ordPullback ρ = G.ordPullback ρW := by
      show (G.E.ordForm (pullbackRationalPluriForms (j ≫ sX) (G.f ≫ pT) ρ) : ℤ) =
        G.E.ordForm (pullbackRationalPluriForms (jW ≫ sW) G.f ρW)
      rw [huniq, ← MMP.Flips.pullbackRationalPluriForms_comp pT G.f hpTbij
        G.isBirationalMorphism.functionFieldMap_bijective hdT ρ,
        pullbackRationalPluriForms_cast G.f hTW, ordForm_cast (congrArg (G.f ≫ ·) hTW)]
      rfl
    exact congrArg _ key

/-- **Monotonicity of adjunction along a nonpositive diagram.** If `p : W ⟶ X`, `q : W ⟶ X'` are
proper birational with `a(E; X, S + Δ) ≤ a(E; X', S' + Δ')` at every prime divisor `E` of `W`, and
`P_W ⊆ W` lies over `S` and `S'`, then `a(G; T, Δ_S) ≤ a(G; T', Δ_{S'})` for every divisor `G`
over `T_W`: computed with the form `p^*τ₀` on `W` and its residue on `T_W`, the difference is the
coefficient along `G` of the pull-back of the effective `ℝ`-Cartier divisor
`p^*(K_X + S + Δ) - q^*(K_{X'} + S' + Δ')`, which does not contain `P_W`. -/
private theorem isLogDiscrepancy_le_of_nonpositive_diagram
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (P : Mori.PrimeDivisor X) (Δ : RDivisor X)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    [IsNormal T] (hj : Set.range j.base = (P.support : Set X)) (ΔS : RDivisor T)
    (hΔS : ∀ τ : RationalPluriForms sX (n + 1) 1, τ ≠ 0 → P.ordForm τ = -1 →
        ∀ ρ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 τ ρ →
          MMP.Flips.IsRCartierPullback j
            (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P 1 + Δ)
            (Divisor.toRDivisor (divisorOfForm ρ) + ΔS))
    {X' T' W TW : Scheme.{0}} (sX' : X' ⟶ Spec (.of ℂ)) [IsIntegral X'] [IsNormal X']
    [IsLocallyNoetherian X'] [CompactSpace X'] [LocallyOfFiniteType sX']
    (hX' : IsNormalVariety ℂ sX') (hdim' : topologicalKrullDim X' = n + 1)
    (P' : Mori.PrimeDivisor X') (Δ' : RDivisor X')
    (j' : T' ⟶ X') [IsClosedImmersion j'] [IsIntegral T'] [IsLocallyNoetherian T']
    [CompactSpace T'] [IsNormal T'] (hj' : Set.range j'.base = (P'.support : Set X'))
    (ΔS' : RDivisor T')
    (hΔS' : ∀ τ : RationalPluriForms sX' (n + 1) 1, τ ≠ 0 → P'.ordForm τ = -1 →
        ∀ ρ : RationalPluriForms (j' ≫ sX') n 1, IsPoincareResidue sX' j' n 1 τ ρ →
          MMP.Flips.IsRCartierPullback j'
            (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P' 1 + Δ')
            (Divisor.toRDivisor (divisorOfForm ρ) + ΔS'))
    (p : W ⟶ X) (q : W ⟶ X') [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsDominant p] [IsDominant q] (hpq : p ≫ sX = q ≫ sX') (hpP : IsProper p) (hqP : IsProper q)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hle : ∀ (E : Mori.PrimeDivisor W) (m : ℕ) (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX')
      (a a' : ℝ), D.valuation = E.valuationOver p → D'.valuation = E.valuationOver q →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) D a →
      MMP.Intersection.IsLogDiscrepancy sX' m (Finsupp.single P' 1 + Δ') D' a' → a ≤ a')
    (PW : Mori.PrimeDivisor W) (hpPW : p PW.genericPoint = P.genericPoint)
    (hqPW : q PW.genericPoint = P'.genericPoint)
    (jW : TW ⟶ W) [IsClosedImmersion jW] [IsIntegral TW]
    (hjW : Set.range jW.base = (PW.support : Set W))
    (pT : TW ⟶ T) (qT : TW ⟶ T') [IsDominant pT] [IsDominant qT]
    (hpT : pT ≫ j = jW ≫ p) (hqT : qT ≫ j' = jW ≫ q)
    (G : DivisorOver ℂ (jW ≫ p ≫ sX)) (D : DivisorOver ℂ (j ≫ sX))
    (D' : DivisorOver ℂ (j' ≫ sX'))
    (hD : D.valuation = G.valuation.comap (functionFieldMap pT))
    (hD' : D'.valuation = G.valuation.comap (functionFieldMap qT))
    (m : ℕ) (a a' : ℝ) (ha : MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m ΔS D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy (j' ≫ sX') m ΔS' D' a') : a ≤ a' := by
  classical
  haveI := hpP
  haveI := hqP
  have hWv : IsNormalVariety ℂ (p ≫ sX) := by
    haveI := hX.1
    exact ⟨⟨⟩, inferInstance⟩
  haveI : LocallyOfFiniteType (p ≫ sX) := hWv.1.toLocallyOfFiniteType
  have hTv : IsNormalVariety ℂ (j ≫ sX) := by
    haveI := hX.1
    exact ⟨⟨⟩, inferInstance⟩
  haveI : LocallyOfFiniteType (j ≫ sX) := hTv.1.toLocallyOfFiniteType
  have hjT := Aux.map_genericPoint_eq j P hj
  have hjWT := Aux.map_genericPoint_eq jW PW hjW
  haveI : IsIso (p.stalkMap PW.genericPoint) :=
    MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb hpPW
  haveI : IsIso (p.stalkMap (jW (genericPoint TW))) :=
    MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb (by rw [hjWT, hpPW])
  have hpTbij := functionFieldMap_bijective_of_comp_eq p j jW pT hpT
  have hpbij := hpb.functionFieldMap_bijective
  have hd : (letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat) = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (letI := functionFieldAlgebra (j ≫ sX);
      (Algebra.trdeg ℂ T.functionField).toNat) = n := by
    have := Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  -- the common form `τ_W = p^*τ₀` on `W` and its residue along `T_W`
  have hT0 : Nonempty (Mori.PrimeDivisor T) := by
    by_contra h
    exact false_of_isEmpty_primeDivisor hTv (not_nonempty_iff.mp h) D
  obtain ⟨τ₀, -, hτ₀, ρ₀, hρ₀, -⟩ :=
    MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue sX hX hdim j hTv P hj hT0.some
  have hτW : PW.ordForm (pullbackRationalPluriForms sX p τ₀) = -1 := by
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hpbij hd PW P hpPW, hτ₀]
  have hρW := MMP.Fourfold.isPoincareResidue_pullback p j jW pT sX hpbij hpTbij hpT P hjT PW
    hjWT hd hdT hρ₀
  -- the two sides
  obtain ⟨k, r, C, hCc, hCP, hCW, C₂, hC₂, ha₂⟩ := exists_side_data sX hX hdim P Δ j hj ΔS hΔS p
    hpb (p ≫ sX) rfl PW hpPW jW hjW pT hpT _ hτW _ hρW G D hD m a ha
  obtain ⟨k', r', C', hCc', hCP', hCW', C₂', hC₂', ha₂'⟩ := exists_side_data sX' hX' hdim' P' Δ' j'
    hj' ΔS' hΔS' q hqb (p ≫ sX) hpq.symm PW hqPW jW hjW qT hqT _ hτW _ hρW G D' hD' m a' ha'
  -- `F = p^*(K_X + S + Δ) - q^*(K_{X'} + S' + Δ')` is effective on `W`
  have hF : ∀ E : Mori.PrimeDivisor W, 0 ≤ (∑ i, r i • Divisor.toRDivisor (C i) +
      ∑ i, (-r' i) • Divisor.toRDivisor (C' i) : RDivisor W).coeff E := by
    intro E
    obtain ⟨DW, hDWv, hDW⟩ := hCW E
    obtain ⟨DW', hDWv', hDW'⟩ := hCW' E
    have := hle E (n + 1) DW DW' _ _ hDWv hDWv' hDW hDW'
    rw [DivisorWithCoeffs.coeff_add, MMP.Flips.coeff_sum_smul_toRDivisor,
      MMP.Flips.coeff_sum_smul_toRDivisor]
    simp only [neg_mul, Finset.sum_neg_distrib]
    linarith
  -- its pull-back to the model of `G` is effective
  haveI := G.isIntegral
  haveI := G.isNormal
  haveI := G.isLocallyNoetherian
  haveI : QuasiCompact (G.f ≫ jW ≫ p ≫ sX) := G.isNormalVariety.1.toQuasiCompact
  haveI : CompactSpace G.Y := QuasiCompact.compactSpace_of_compactSpace (G.f ≫ jW ≫ p ≫ sX)
  have hpbF : MMP.Flips.IsRCartierPullback (G.f ≫ jW)
      (∑ i, r i • Divisor.toRDivisor (C i) + ∑ i, (-r' i) • Divisor.toRDivisor (C' i))
      (∑ i, r i • Divisor.toRDivisor (C₂ i) + ∑ i, (-r' i) • Divisor.toRDivisor (C₂' i)) := by
    refine MMP.Fourfold.isRCartierPullback_add
      (MMP.Fourfold.isRCartierPullback_sum _ _ _ fun i _ => ?_)
      (MMP.Fourfold.isRCartierPullback_sum _ _ _ fun i _ => ?_)
    · obtain ⟨hB, hp⟩ := hC₂ i
      exact MMP.Fourfold.isRCartierPullback_smul _
        (MMP.Fourfold.isRCartierPullback_toRDivisor (hCc i) hB hp)
    · obtain ⟨hB, hp⟩ := hC₂' i
      exact MMP.Fourfold.isRCartierPullback_smul _
        (MMP.Fourfold.isRCartierPullback_toRDivisor (hCc' i) hB hp)
  have hE := coeff_nonneg_of_isRCartierPullback' (G.f ≫ jW) hpbF hF G.E
  rw [DivisorWithCoeffs.coeff_add, MMP.Flips.coeff_sum_smul_toRDivisor,
    MMP.Flips.coeff_sum_smul_toRDivisor] at hE
  simp only [neg_mul, Finset.sum_neg_distrib] at hE
  rw [ha₂, ha₂']
  linarith

end Monotonicity

/-- An integral scheme of dimension zero is normal: it is a point, whose local ring is the
function field. -/
private theorem isNormal_of_topologicalKrullDim_eq_zero {T : Scheme.{0}} [IsIntegral T]
    (h : topologicalKrullDim T = 0) : IsNormal T := by
  let _ : PartialOrder T := specializationOrder T
  have hk : Order.krullDim T = 0 := by
    rw [← h]
    exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := T))).symm
  have hgen : ∀ x : T, x = genericPoint T := by
    intro x
    by_contra hx
    have hlt : x < genericPoint T :=
      lt_of_le_of_ne ((genericPoint_spec T).specializes trivial) hx
    have h1 : Order.coheight x ≠ 0 := fun h0 =>
      (Order.coheight_eq_zero.mp h0).not_lt hlt
    have h2 := Order.coheight_le_krullDim x
    rw [hk] at h2
    have h3 : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := h2
    exact h1 (nonpos_iff_eq_zero.mp (WithBot.coe_le_coe.mp h3))
  refine ⟨fun x => inferInstance, fun x => ?_⟩
  obtain rfl := hgen x
  change IsIntegrallyClosed T.functionField
  infer_instance

/-- **Normality of the plt centre** (Kollár–Mori 5.52). The reduced pair `(X, S)` is dlt with
round down `S`, so `S` is normal; a point is normal. -/
private theorem isNormal_of_real_plt
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hQ : IsQFactorial sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (P : Mori.PrimeDivisor X) (Δ : RDivisor X)
    (hΔ : ∀ Q, 0 ≤ Δ.coeff Q ∧ Δ.coeff Q ≤ 1) (hΔP : Δ.coeff P = 0)
    (hcart : ∃ (m : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX m ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + Finsupp.single P 1 + Δ))
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) E a → 0 < a)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (hj : Set.range j.base = (P.support : Set X))
    (km5b : ∀ {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
      [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
      [IsAlgClosed k] [CharZero k] (h : IsDltPair sX n K Δ) (hn : 2 ≤ n) (hΔ : 0 ≤ Δ)
      (P : Mori.PrimeDivisor X) (hP : Δ.roundDown.coeff P ≠ 0),
      IsNormal P.idealSheaf.subscheme) : IsNormal T := by
  have hX : IsNormalVariety ℂ sX := hQ.1
  haveI : LocallyOfFiniteType (j ≫ sX) := by
    haveI := hX.1
    infer_instance
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `S` is a point
    refine isNormal_of_topologicalKrullDim_eq_zero ?_
    rw [topologicalKrullDim_eq_of_isClosedImmersion sX j P hj hdim]
    rfl
  -- the reduced pair `(X, S)` is dlt
  obtain ⟨m₀, K, hK, -⟩ := hcart
  obtain rfl : m₀ = n + 1 := by
    have := hK.topologicalKrullDim_eq
    rw [hdim] at this
    exact_mod_cast this.symm
  have hdlt := isDltPair_add_single hQ hplt hK 0 le_rfl rfl (fun _ => zero_lt_one)
    (fun Q => by simpa using (hΔ Q).1)
  have hfloor : DivisorWithCoeffs.coeff
      (DivisorWithCoeffs.roundDown (Finsupp.single P 1 + 0 : QDivisor X)) P ≠ 0 := by
    rw [DivisorWithCoeffs.coeff_roundDown, add_zero, DivisorWithCoeffs.coeff_apply,
      Finsupp.single_eq_same]
    norm_num
  have hnorm : IsNormal P.idealSheaf.subscheme :=
    km5b hdlt (by omega) (by rw [add_zero]; exact Finsupp.single_nonneg.mpr zero_le_one) P hfloor
  -- transport to `T ≅ P.idealSheaf.subscheme`
  have hk : j.ker = P.idealSheaf.subschemeι.ker := by
    rw [MMP.Mori.PrimeDivisor.ker_eq_idealSheaf_of_range_eq j P hj,
      Scheme.IdealSheafData.ker_subschemeι]
  haveI := IsClosedImmersion.isIso_lift j P.idealSheaf.subschemeι hk
  exact isNormal_of_isOpenImmersion (inv (IsClosedImmersion.lift j P.idealSheaf.subschemeι hk.le))

/-- The log discrepancy of a prime divisor `P` of `X` with respect to an `ℝ`-divisor `B` with
`K + B` `ℝ`-Cartier is `1 - coeff_P B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX P)
      (1 - B.coeff P) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) (hC i)
  have hC'P : ∀ i, (C' i).coeff P = (C i).coeff P := fun i =>
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) P P rfl (hC i) (hC' i)
  have hord : (DivisorOver.ofPrimeDivisor ℂ hX P).ordPullback ω = P.ordForm ω :=
    DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P ω
  have hsumΓ : ∀ Γ, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ := fun Γ => by
    rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
  refine ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C,
    C', hC, hsumΓ, fun i => ⟨_, hC' i⟩, ?_⟩
  change 1 - B.coeff P = 1 + ((DivisorOver.ofPrimeDivisor ℂ hX P).ordPullback ω : ℝ) -
    ∑ i, r i * ((C' i).coeff P : ℝ)
  simp_rw [hC'P, hord]
  rw [← hsumΓ P]
  ring

/-! ### The real different is klt -/

section RealKlt

variable {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
  [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
  (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
  [CompactSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
  {n : ℕ} (hX : IsNormalVariety ℂ sX) (hdim : topologicalKrullDim X = n + 1)
  (hT : IsNormalVariety ℂ (j ≫ sX)) (hdimT : topologicalKrullDim T = n) (hQ : IsQFactorial sX)
  {R : Mori.PrimeDivisor X → QDivisor T}
  (hR : ∀ Q, Q ≠ P → R Q ≥ 0 ∧
      ∃ hgen : ∀ Z : irreducibleComponents T,
          j (componentGenericPoint T Z) ∉ DivisorWithCoeffs.supp (Finsupp.single Q (1 : ℚ) : QDivisor X),
        QDivisor.IsPullback j (Finsupp.single Q (1 : ℚ) : QDivisor X) hgen (R Q))
  {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0) (hτ₀ : P.ordForm τ₀ = -1)
  (hK₀ : (divisorOfForm τ₀).IsCanonicalDivisor sX (n + 1))
  {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀)
  (hρ₀0 : ρ₀ ≠ 0) (hKρ₀ : (divisorOfForm ρ₀).IsCanonicalDivisor (j ≫ sX) n)
  {BS₀ : QDivisor T}
  (hBS₀ : ∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
        (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + 0 : QDivisor X).supp,
      (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 + 0 : QDivisor X).IsPullback j
        hgen (Divisor.toQDivisor (divisorOfForm ρ₀) + BS₀))

include hQ hR hBS₀ in
/-- The residue identity for a rational boundary `B = ∑_{Q ∈ s} b_Q Q` without `S`-component:
`(div τ₀ + S + B)|_S = div ρ₀ + B_S⁰ + ∑ b_Q R_Q`. -/
private theorem isRCartierPullback_rationalDifferent (s : Finset (Mori.PrimeDivisor X))
    (b : Mori.PrimeDivisor X → ℚ) (hs : ∀ Q ∈ s, Q ≠ P) :
    MMP.Flips.IsRCartierPullback j
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm τ₀) + Finsupp.single P 1 +
        ∑ Q ∈ s, b Q • Finsupp.single Q (1 : ℚ)))
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm ρ₀) +
        (BS₀ + ∑ Q ∈ s, b Q • R Q))) := by
  obtain ⟨_, hpb₀⟩ := hBS₀
  convert MMP.Fourfold.isRCartierPullback_add
    (isRCartierPullback_of_isPullback j (isQCartier_of_isQFactorial sX hQ _) hpb₀)
    (isRCartierPullback_sum_smul_restrict sX j P hQ hR s hs fun Q => (b Q : ℝ)) using 1 <;>
    simp only [map_add, map_zero, add_zero, map_sum, toRDivisor_smul, add_assoc]

include hP hX hdim hT hdimT hQ hR hτ₀0 hτ₀ hK₀ hρ₀ hρ₀0 hKρ₀ hBS₀ in
/-- **Rational adjunction for `S + ∑ b_Q Q`.** If `S + ∑_{Q ∈ s} b_Q Q`, `b ≥ 0`, has positive
log discrepancies along exceptional divisors, then `(S, B_S⁰ + ∑ b_Q R_Q)` is klt. -/
private theorem pos_of_isLogDiscrepancy_rationalDifferent (s : Finset (Mori.PrimeDivisor X))
    (b : Mori.PrimeDivisor X → ℚ) (hs : ∀ Q ∈ s, Q ≠ P) (hb : ∀ Q, 0 ≤ b Q)
    (hpos : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (QDivisor.toRDivisor
        (Finsupp.single P 1 + ∑ Q ∈ s, b Q • Finsupp.single Q (1 : ℚ))) E a → 0 < a)
    (m : ℕ) (F : DivisorOver ℂ (j ≫ sX)) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m
      (QDivisor.toRDivisor (BS₀ + ∑ Q ∈ s, b Q • R Q)) F a) : 0 < a := by
  classical
  refine pos_of_isLogDiscrepancy_residueDifferent sX j P hP hX hdim hT hdimT hQ
    (fun G => by
      change (0 : ℚ) ≤ (∑ Q ∈ s, b Q • Finsupp.single Q (1 : ℚ)) G
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_nonneg fun Q _ => ?_
      rw [Finsupp.smul_apply, Finsupp.single_apply]
      split_ifs <;> simp [hb Q]) ?_ hpos hτ₀0 hτ₀ hK₀ hρ₀ hρ₀0 hKρ₀
    (isRCartierPullback_rationalDifferent sX j P hQ hR hBS₀ s b hs) m F a ha
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero fun Q hQs => by
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (hs Q hQs).symm, smul_zero]

include hP hX hdim hT hdimT hQ hR hτ₀0 hτ₀ hK₀ hρ₀ hρ₀0 hKρ₀ hBS₀ in
/-- **Components of coefficient one do not meet `S`.** If `(X, S + Δ)` is plt and `δ_Q = 1`, then
`Q|_S = 0`: otherwise the rational pair `(S, B_S⁰ + R_Q)`, klt by adjunction from `S + Q`, would
have a coefficient `1 - (1 - r_Q) / m ≥ 1`. -/
private theorem restrict_eq_zero_of_coeff_eq_one {Δ : RDivisor X}
    (hΔ : ∀ Q, 0 ≤ Δ.coeff Q ∧ Δ.coeff Q ≤ 1) (hΔP : Δ.coeff P = 0)
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) E a → 0 < a)
    (hn1 : 1 ≤ n) {Q : Mori.PrimeDivisor X} (hQΔ : Q ∈ Δ.support) (hδ1 : Δ.coeff Q = 1) :
    R Q = 0 := by
  classical
  ext Q'
  obtain ⟨m, hm, r, hB0c, hRc⟩ := exists_coeff_residueDifferent_eq sX j P hP hX hdim hT hQ hΔ
    hΔP hplt hn1 hR hτ₀0 hτ₀ hK₀ hρ₀ hBS₀ Q'
  have hs : ∀ G ∈ ({Q} : Finset _), G ≠ P := fun G hG =>
    Finset.mem_singleton.mp hG ▸ ne_of_mem_support hΔP hQΔ
  have hpos := pos_of_isLogDiscrepancy_of_le_of_isExceptional hQ (Δ' := Finsupp.single P 1 + Δ)
    (B := QDivisor.toRDivisor (Finsupp.single P 1 +
      ∑ G ∈ ({Q} : Finset _), (1 : ℚ) • Finsupp.single G (1 : ℚ))) (fun G => by
      rw [Finset.sum_singleton, one_smul, QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
        DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply,
        Finsupp.single_apply, Finsupp.single_apply]
      have := (hΔ G).1
      rw [DivisorWithCoeffs.coeff_apply] at this hδ1
      split_ifs with h1 h2 h2 <;> push_cast <;> subst_vars <;> simp_all) hplt
  obtain ⟨m', r', L, L', hL, -, hL', hG⟩ :=
    isRCartierPullback_rationalDifferent sX j P hQ hR hBS₀ {Q} (fun _ => 1) hs
  have hRCQ : RDivisor.IsRCartier (Divisor.toRDivisor (divisorOfForm ρ₀) +
      QDivisor.toRDivisor (BS₀ + ∑ G ∈ ({Q} : Finset _), (1 : ℚ) • R G)) := by
    refine ⟨m', r', L', fun i => (hL' i).2.isCartier (hL i), fun Γ => ?_⟩
    rw [← QDivisor.toRDivisor_toQDivisor, ← map_add, hG, MMP.Flips.coeff_sum_smul_toRDivisor]
  have hlt := pos_of_isLogDiscrepancy_rationalDifferent sX j P hP hX hdim hT hdimT hQ hR hτ₀0 hτ₀
    hK₀ hρ₀ hρ₀0 hKρ₀ hBS₀ {Q} (fun _ => 1) hs (fun _ => zero_le_one) hpos n _ _
    (isLogDiscrepancy_ofPrimeDivisor hT hKρ₀ hRCQ Q')
  rw [Finset.sum_singleton, one_smul, QDivisor.coeff_toRDivisor,
    DivisorWithCoeffs.coeff_add, hB0c, hRc Q hQΔ] at hlt
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hr : (r Q : ℝ) < 1 := by
    have : ((r Q : ℚ) : ℝ) / m < 1 / m := by push_cast at hlt ⊢; linarith
    rwa [div_lt_div_iff_of_pos_right hm0] at this
  have hr0 : r Q = 0 := by exact_mod_cast (Nat.lt_one_iff.mp (by exact_mod_cast hr))
  rw [hRc Q hQΔ, hr0]
  simp

include hP hX hdim hT hdimT hQ hR hτ₀0 hτ₀ hK₀ hρ₀ hρ₀0 hKρ₀ hBS₀ in
/-- **The real different is klt** (real adjunction). If `(X, S + Δ)` is plt, then
`(S, Δ_S)`, `Δ_S = B_S⁰ + ∑ δ_Q R_Q`, is klt. The components with `δ_Q = 1` do not meet `S`. The
remaining coefficient vector `δ` lies in an open set of vectors `x` with `S + ∑ x_Q Q` plt, so
`δ` is a convex combination of rational vectors `b` there; each `(S, B_S⁰ + ∑ b_Q R_Q)` is klt by
rational adjunction, and the klt region along the `ℚ`-Cartier `R_Q` is convex. -/
private theorem pos_of_isLogDiscrepancy_realDifferent {Δ : RDivisor X}
    (hΔ : ∀ Q, 0 ≤ Δ.coeff Q ∧ Δ.coeff Q ≤ 1) (hΔP : Δ.coeff P = 0)
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) E a → 0 < a)
    (hn1 : 1 ≤ n) (m : ℕ) (F : DivisorOver ℂ (j ≫ sX)) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m
      (QDivisor.toRDivisor BS₀ + ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q)) F a) :
    0 < a := by
  classical
  have hRq : ∀ Q, Q ≠ P → (R Q).IsQCartier := fun Q hQP => by
    obtain ⟨-, hg, hp⟩ := hR Q hQP
    obtain ⟨m, hm, D, hD, hDc⟩ :=
      (isQCartier_of_isQFactorial sX hQ (Finsupp.single Q (1 : ℚ) : QDivisor X)).exists_pos
    obtain ⟨D', hD', hD'p⟩ := hp m hm D hD hDc
    exact ⟨m, by exact_mod_cast hm.ne', D', hD', hD'p.isCartier hDc⟩
  -- the components with coefficient `< 1`
  set s := Δ.support.filter (fun Q => Δ.coeff Q < 1)
  have hsP : ∀ Q ∈ s, Q ≠ P := fun Q hQ => ne_of_mem_support hΔP (Finset.mem_filter.mp hQ).1
  have hsplit : (∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q)) =
      ∑ Q ∈ s, Δ.coeff Q • QDivisor.toRDivisor (R Q) := by
    rw [← Finset.sum_filter_add_sum_filter_not Δ.support (fun Q => Δ.coeff Q < 1),
      Finset.sum_eq_zero (s := Δ.support.filter (fun Q => ¬ Δ.coeff Q < 1)) fun Q hQs => ?_,
      add_zero]
    obtain ⟨hQΔ, hQ1⟩ := Finset.mem_filter.mp hQs
    rw [restrict_eq_zero_of_coeff_eq_one sX j P hP hX hdim hT hdimT hQ hR hτ₀0 hτ₀ hK₀ hρ₀ hρ₀0
      hKρ₀ hBS₀ hΔ hΔP hplt hn1 hQΔ (le_antisymm (hΔ Q).2 (not_lt.mp hQ1)), map_zero, smul_zero]
  rw [hsplit, ← Finset.sum_coe_sort s] at ha
  let x : s → ℝ := fun i => Δ.coeff i
  have hx1 : ∀ i, x i < 1 := fun i => (Finset.mem_filter.mp i.2).2
  have hx0 : ∀ i, 0 < x i := fun i => lt_of_le_of_ne (hΔ i).1
    (Ne.symm (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp i.2).1))
  have hcoeffsum : ∀ (y : s → ℝ) (G : Mori.PrimeDivisor X),
      (∑ i : s, Finsupp.single (i : Mori.PrimeDivisor X) (y i) : RDivisor X).coeff G =
        if h : G ∈ s then y ⟨G, h⟩ else 0 := by
    intro y G
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    split_ifs with h
    · rw [Fintype.sum_eq_single ⟨G, h⟩ fun i hi =>
        Finsupp.single_eq_of_ne (fun e => hi (Subtype.ext e.symm)), Finsupp.single_eq_same]
    · exact Finset.sum_eq_zero fun i _ =>
        Finsupp.single_eq_of_ne (fun e => h (by rw [e]; exact i.2))
  have hpltx := pos_of_isLogDiscrepancy_of_le_of_isExceptional hQ
    (Δ' := Finsupp.single P 1 + Δ)
    (B := Finsupp.single P 1 + ∑ i : s, Finsupp.single (i : Mori.PrimeDivisor X) (x i)) (fun G => by
      rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hcoeffsum]
      split_ifs with h
      · exact le_rfl
      · linarith [(hΔ G).1]) hplt
  obtain ⟨U, hU, hUq⟩ := exists_nhds_pos_isLogDiscrepancy hQ (fun i : s => (i : Mori.PrimeDivisor X))
    Subtype.val_injective P (fun i => hsP i i.2) hK₀ x hx1 hpltx
  have hU' : U ∩ {y | ∀ i, 0 < y i} ∈ nhds x := by
    refine Filter.inter_mem hU ?_
    have : ∀ i, {y : s → ℝ | 0 < y i} ∈ nhds x := fun i =>
      ((continuous_apply i).isOpen_preimage _ isOpen_Ioi).mem_nhds (hx0 i)
    exact Filter.mem_of_superset (Filter.iInter_mem.mpr this) fun y hy i => Set.mem_iInter.mp hy i
  obtain ⟨V, hV, hVx⟩ := MMP.Fourfold.exists_rat_convexHull_mem_nhds hU'
  have hconv := convex_setOf_pos_isLogDiscrepancy_add (j ≫ sX) (QDivisor.toRDivisor BS₀)
    (fun i : s => R i) (fun i => hRq i (hsP i i.2))
  have hVK : V ⊆ {y : s → ℝ | ∀ (m : ℕ) (F : DivisorOver ℂ (j ≫ sX)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m
        (QDivisor.toRDivisor BS₀ + ∑ i, y i • QDivisor.toRDivisor (R i)) F a → 0 < a} := by
    intro v hv
    obtain ⟨⟨hvU, hvpos⟩, q, rfl⟩ := hV v hv
    let b : Mori.PrimeDivisor X → ℚ := fun Q => if h : Q ∈ s then q ⟨Q, h⟩ else 0
    have hb0 : ∀ Q, 0 ≤ b Q := fun Q => by
      simp only [b]
      split_ifs with h
      · have := (hvpos ⟨Q, h⟩).le
        simp only at this
        exact_mod_cast this
      · exact le_rfl
    have hbi : ∀ i : s, b i = q i := fun i => by simp only [b, dif_pos i.2]
    have hBeq : QDivisor.toRDivisor (Finsupp.single P 1 + ∑ Q ∈ s, b Q • Finsupp.single Q (1 : ℚ)) =
        Finsupp.single P 1 + ∑ i : s, Finsupp.single (i : Mori.PrimeDivisor X) ((q i : ℝ)) := by
      rw [map_add, toRDivisor_single_one, map_sum, ← Finset.sum_coe_sort s]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [toRDivisor_smul, toRDivisor_single_one, Finsupp.smul_single_one, hbi]
    have hBSeq : QDivisor.toRDivisor (BS₀ + ∑ Q ∈ s, b Q • R Q) =
        QDivisor.toRDivisor BS₀ + ∑ i, ((q i : ℚ) : ℝ) • QDivisor.toRDivisor (R i) := by
      rw [map_add, map_sum, ← Finset.sum_coe_sort s]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [toRDivisor_smul, hbi]
    intro m F a ha
    exact pos_of_isLogDiscrepancy_rationalDifferent sX j P hP hX hdim hT hdimT hQ hR hτ₀0 hτ₀ hK₀
      hρ₀ hρ₀0 hKρ₀ hBS₀ s b hsP hb0 (fun m E a hE hEa => hUq q hvU m E a hE (hBeq ▸ hEa)) m F a
      (hBSeq ▸ ha)
  exact convexHull_min hVK hconv (mem_of_mem_nhds hVx) m F a ha

include hP hX hdim hT hQ hR hτ₀0 hτ₀ hK₀ hρ₀ hBS₀ in
/-- **The coefficients of the real different are of hyperstandard type.** If the coefficients of
`Δ` in `(0, 1)` lie in a finite set `I` and `coeff_{Q'} Δ_S < 1`, then
`coeff_{Q'} Δ_S = 1 - (1 - ∑_{b ∈ I} n_b b) / m` with `m ≥ 1` and `∑ n_b b < 1`. -/
private theorem exists_coeff_realDifferent_eq {Δ : RDivisor X}
    (hΔ : ∀ Q, 0 ≤ Δ.coeff Q ∧ Δ.coeff Q ≤ 1) (hΔP : Δ.coeff P = 0)
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) E a → 0 < a)
    (hn1 : 1 ≤ n) (I : Finset ℝ) (hΔI : ∀ Q, 0 < Δ.coeff Q → Δ.coeff Q ∈ I)
    (Q' : Mori.PrimeDivisor T)
    (hlt1 : (QDivisor.toRDivisor BS₀ +
      ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q)).coeff Q' < 1) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c : ℝ → ℕ, ∑ b ∈ I, (c b : ℝ) * b < 1 ∧
      (QDivisor.toRDivisor BS₀ + ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q)).coeff Q' =
        1 - (1 - ∑ b ∈ I, (c b : ℝ) * b) / m := by
  classical
  obtain ⟨m, hm, r, hB0c, hRc⟩ := exists_coeff_residueDifferent_eq sX j P hP hX hdim hT hQ hΔ
    hΔP hplt hn1 hR hτ₀0 hτ₀ hK₀ hρ₀ hBS₀ Q'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hval : (QDivisor.toRDivisor BS₀ +
      ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q)).coeff Q' =
      1 - (1 - ∑ Q ∈ Δ.support, (r Q : ℝ) * Δ.coeff Q) / m := by
    rw [coeff_residueDifferent, hB0c]
    have hs : ∑ Q ∈ Δ.support, Δ.coeff Q * (((R Q).coeff Q' : ℚ) : ℝ) =
        (∑ Q ∈ Δ.support, (r Q : ℝ) * Δ.coeff Q) / m := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [hRc Q hQ]
      push_cast
      ring
    rw [hs]
    push_cast
    field_simp
    ring
  have hsumI : ∑ b ∈ I, ((∑ Q ∈ Δ.support with Δ.coeff Q = b, r Q : ℕ) : ℝ) * b =
      ∑ Q ∈ Δ.support, (r Q : ℝ) * Δ.coeff Q := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun Q => Δ.coeff Q) (t := I) fun Q hQ =>
      hΔI Q (lt_of_le_of_ne (hΔ Q).1 (Ne.symm (Finsupp.mem_support_iff.mp hQ)))]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [(Finset.mem_filter.mp hQ).2]
  refine ⟨m, hm, fun b => ∑ Q ∈ Δ.support with Δ.coeff Q = b, r Q, ?_, by rw [hval, hsumI]⟩
  rw [hsumI]
  rw [hval] at hlt1
  have h2 : 0 < (1 - ∑ Q ∈ Δ.support, (r Q : ℝ) * Δ.coeff Q) / m := by linarith
  have := (div_pos_iff_of_pos_right hm0).mp h2
  linarith

end RealKlt

/-- **Adjunction to the reduced component of a real plt pair.** Let `X` be a `ℚ`-factorial normal
complex variety of dimension `n + 1`, `P` a prime divisor with reduced closed subscheme
`j : T ⟶ X`, and `Δ` an `ℝ`-divisor with coefficients in `[0, 1]` and `coeff_P Δ = 0` such that
`(X, P + Δ)` is real plt. Then the coefficient sets `{1 - (1 - ∑_{b ∈ I} n_b b) / m}`
(`m ≥ 1`, `n_b ∈ ℕ`, `∑ n_b b < 1`) of finite `I ⊂ (0, 1)` are well-founded, `T` is normal, and
there is an `ℝ`-divisor `Δ_S` on `T` with `div(ρ) + Δ_S = (div(τ) + P + Δ)|_T` for every rational
top form `τ` with `ord_P τ = -1` and Poincaré residue `ρ` of `τ` along `T`. Every such `Δ_S` is
effective and klt; its coefficients lie in the coefficient set of `I` when the positive
coefficients of `Δ` lie in `I`; `A|_T ≤ Δ_S` for an effective `ℚ`-Cartier `A ≤ Δ` not containing
`P`; and for a second such pair `(X', P' + Δ')` with different `Δ_{S'}` on `T'`, proper
birational `p : W ⟶ X`, `q : W ⟶ X'` over `ℂ` with `a(E; X, P + Δ) ≤ a(E; X', P' + Δ')` for every
prime divisor `E` of `W`, and a prime divisor `P_W` of `W` over `P` and `P'`, with closed
subscheme `T_W` and induced `p_T : T_W ⟶ T`, `q_T : T_W ⟶ T'`, one has
`a(v; T, Δ_S) ≤ a(v; T', Δ_{S'})` for every divisor `v` over `T_W`. -/
@[mmp "lem_fourfold_real_plt_adjunction"]
public theorem _root_.MMP.Fourfold.exists_isNormal_isRCartierPullback_isPoincareResidue
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hQ : IsQFactorial sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (P : Mori.PrimeDivisor X) (Δ : RDivisor X)
    (hΔ : ∀ Q, 0 ≤ Δ.coeff Q ∧ Δ.coeff Q ≤ 1) (hΔP : Δ.coeff P = 0)
    (hcart : ∃ (m : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX m ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + Finsupp.single P 1 + Δ))
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) E a → 0 < a)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (hj : Set.range j.base = (P.support : Set X)) :
    (∀ I : Finset ℝ, (∀ b ∈ I, b ∈ Set.Ioo (0 : ℝ) 1) →
      Set.IsWF {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ ∃ c : ℝ → ℕ, ∑ b ∈ I, (c b : ℝ) * b < 1 ∧
        x = 1 - (1 - ∑ b ∈ I, (c b : ℝ) * b) / m}) ∧
    ∃ hT : IsNormal T,
      (∃ ΔS : RDivisor T, ∀ τ : RationalPluriForms sX (n + 1) 1, τ ≠ 0 → P.ordForm τ = -1 →
        ∀ ρ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 τ ρ →
          MMP.Flips.IsRCartierPullback j
            (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P 1 + Δ)
            (Divisor.toRDivisor (divisorOfForm ρ) + ΔS)) ∧
      ∀ ΔS : RDivisor T, (∀ τ : RationalPluriForms sX (n + 1) 1, τ ≠ 0 → P.ordForm τ = -1 →
        ∀ ρ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 τ ρ →
          MMP.Flips.IsRCartierPullback j
            (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P 1 + Δ)
            (Divisor.toRDivisor (divisorOfForm ρ) + ΔS)) →
        -- `Δ_S` is an effective klt boundary
        ΔS.IsEffective ∧
        (IsNormalVariety ℂ (j ≫ sX) ∧
          (∃ (m : ℕ) (K : Divisor T), K.IsCanonicalDivisor (j ≫ sX) m ∧
            RDivisor.IsRCartier (Divisor.toRDivisor K + ΔS)) ∧
          ∀ (m : ℕ) (E : DivisorOver ℂ (j ≫ sX)) (a : ℝ),
            MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m ΔS E a → 0 < a) ∧
        -- the coefficients of `Δ_S`
        (∀ I : Finset ℝ, (∀ b ∈ I, b ∈ Set.Ioo (0 : ℝ) 1) →
          (∀ Q, 0 < Δ.coeff Q → Δ.coeff Q ∈ I) →
          ∀ Q : Mori.PrimeDivisor T, ∃ m : ℕ, 1 ≤ m ∧ ∃ c : ℝ → ℕ,
            ∑ b ∈ I, (c b : ℝ) * b < 1 ∧ ΔS.coeff Q = 1 - (1 - ∑ b ∈ I, (c b : ℝ) * b) / m) ∧
        -- the different contains `A|_S`
        (∀ A : QDivisor X, A.IsEffective → A.IsQCartier →
          (∀ Q, (A.coeff Q : ℝ) ≤ Δ.coeff Q) → A.coeff P = 0 →
          ∀ (hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ A.supp)
            (AS : QDivisor T), A.IsPullback j hgen AS →
          ∀ Q : Mori.PrimeDivisor T, (AS.coeff Q : ℝ) ≤ ΔS.coeff Q) ∧
        -- monotonicity along nonpositive plt diagrams retaining `S`
        (∀ {X' T' W TW : Scheme.{0}} (sX' : X' ⟶ Spec (.of ℂ)) [IsIntegral X'] [IsNormal X']
          [IsLocallyNoetherian X'] [CompactSpace X'] [LocallyOfFiniteType sX'],
          IsQFactorial sX' → topologicalKrullDim X' = n + 1 →
          ∀ (P' : Mori.PrimeDivisor X') (Δ' : RDivisor X'),
          (∀ Q, 0 ≤ Δ'.coeff Q ∧ Δ'.coeff Q ≤ 1) → Δ'.coeff P' = 0 →
          (∃ (m : ℕ) (K : Divisor X'), K.IsCanonicalDivisor sX' m ∧
            RDivisor.IsRCartier (Divisor.toRDivisor K + Finsupp.single P' 1 + Δ')) →
          (∀ (m : ℕ) (E : DivisorOver ℂ sX') (a : ℝ), E.IsExceptional →
            MMP.Intersection.IsLogDiscrepancy sX' m (Finsupp.single P' 1 + Δ') E a → 0 < a) →
          ∀ (j' : T' ⟶ X') [IsClosedImmersion j'] [IsIntegral T'] [IsLocallyNoetherian T']
            [CompactSpace T'] [IsNormal T'], Set.range j'.base = (P'.support : Set X') →
          ∀ ΔS' : RDivisor T',
            (∀ τ : RationalPluriForms sX' (n + 1) 1, τ ≠ 0 → P'.ordForm τ = -1 →
              ∀ ρ : RationalPluriForms (j' ≫ sX') n 1, IsPoincareResidue sX' j' n 1 τ ρ →
                MMP.Flips.IsRCartierPullback j'
                  (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P' 1 + Δ')
                  (Divisor.toRDivisor (divisorOfForm ρ) + ΔS')) →
          ∀ (p : W ⟶ X) (q : W ⟶ X') [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
            [IsDominant p] [IsDominant q], p ≫ sX = q ≫ sX' → IsProper p → IsProper q →
            IsBirationalMorphism p → IsBirationalMorphism q →
          (∀ (E : Mori.PrimeDivisor W) (m : ℕ) (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX')
            (a a' : ℝ), D.valuation = E.valuationOver p → D'.valuation = E.valuationOver q →
            MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) D a →
            MMP.Intersection.IsLogDiscrepancy sX' m (Finsupp.single P' 1 + Δ') D' a' → a ≤ a') →
          ∀ PW : Mori.PrimeDivisor W, p PW.genericPoint = P.genericPoint →
            q PW.genericPoint = P'.genericPoint →
          ∀ (jW : TW ⟶ W) [IsClosedImmersion jW] [IsIntegral TW],
            Set.range jW.base = (PW.support : Set W) →
          ∀ (pT : TW ⟶ T) (qT : TW ⟶ T') [IsDominant pT] [IsDominant qT],
            pT ≫ j = jW ≫ p → qT ≫ j' = jW ≫ q →
          ∀ (G : DivisorOver ℂ (jW ≫ p ≫ sX)) (D : DivisorOver ℂ (j ≫ sX))
            (D' : DivisorOver ℂ (j' ≫ sX')),
            D.valuation = G.valuation.comap (functionFieldMap pT) →
            D'.valuation = G.valuation.comap (functionFieldMap qT) →
          ∀ (m : ℕ) (a a' : ℝ), MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m ΔS D a →
            MMP.Intersection.IsLogDiscrepancy (j' ≫ sX') m ΔS' D' a' → a ≤ a') := by
  have hX : IsNormalVariety ℂ sX := hQ.1
  haveI hTn : IsNormal T := isNormal_of_real_plt sX hQ hdim P Δ hΔ hΔP hcart hplt j hj
    (fun h hn hΔ P hP => h.isNormal_subscheme_of_coeff_roundDown_ne_zero hn hΔ P hP)
  refine ⟨fun I hI => isWF_setOf_one_sub_div I hI, hTn, ?_⟩
  have hTv : IsNormalVariety ℂ (j ≫ sX) := by
    have := hX.1
    exact ⟨⟨⟩, inferInstance⟩
  haveI : LocallyOfFiniteType (j ≫ sX) := hTv.1.toLocallyOfFiniteType
  have hdimT := topologicalKrullDim_eq_of_isClosedImmersion sX j P hj hdim
  obtain ⟨R, hR⟩ := exists_restrict_primeDivisor sX j P hj hQ
  by_cases hT0 : Nonempty (Mori.PrimeDivisor T)
  swap
  · -- `S` is a point: every divisor on it is zero and no divisor lies over it
    haveI hE : IsEmpty (Mori.PrimeDivisor T) := not_nonempty_iff.mp hT0
    have hsub : ∀ G : RDivisor T, G = 0 := fun G => Finsupp.ext fun Q => isEmptyElim Q
    refine ⟨⟨0, fun τ hτ0 hτ ρ hρ => ?_⟩, fun ΔS hΔS => ?_⟩
    · have h1 := isRCartierPullback_of_isPullback j (isQCartier_of_isQFactorial sX hQ _)
        (QDivisor.isPullback_pullback (f := j) (isQCartier_of_isQFactorial sX hQ _)
          (map_componentGenericPoint_notMem_supp_divisorOfForm_add sX j P hj hτ (B := 0) rfl))
      have h2 := isRCartierPullback_sum_smul_restrict sX j P hQ hR Δ.support
        (fun _ => ne_of_mem_support hΔP) Δ.coeff
      rw [sum_coeff_smul_single_eq] at h2
      have h3 := MMP.Fourfold.isRCartierPullback_add h1 h2
      rw [map_add, map_add, map_zero, add_zero, QDivisor.toRDivisor_toQDivisor,
        toRDivisor_single_one] at h3
      convert h3 using 1
      exact (hsub _).trans (hsub _).symm
    · rw [hsub ΔS]
      refine ⟨fun Q => isEmptyElim Q, ⟨hTv, ?_, fun m E a _ =>
        (false_of_isEmpty_primeDivisor hTv hE E).elim⟩, fun I _ _ Q => isEmptyElim Q,
        fun _ _ _ _ _ _ _ _ Q => isEmptyElim Q, ?_⟩
      · obtain ⟨K₁, hK₁⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (j ≫ sX) hTv hdimT
        exact ⟨n, K₁, hK₁, ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun Γ => isEmptyElim Γ⟩⟩
      · intros
        exact (false_of_isEmpty_primeDivisor hTv hE ‹DivisorOver ℂ (j ≫ sX)›).elim
  obtain ⟨Q₀⟩ := hT0
  obtain ⟨τ₀, hτ₀0, hτ₀, ρ₀, hρ₀, hρ₀0⟩ :=
    MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue sX hX hdim j hTv P hj Q₀
  obtain ⟨BS₀, hBS₀, hpb, -⟩ := exists_isEffective_isPullback_divisorOfForm_isPoincareResidue sX hX
    hdim j hTv P hj 0 (fun _ => le_rfl) rfl τ₀ hτ₀0 hτ₀ ρ₀ hρ₀
    (isQCartier_of_isQFactorial sX hQ _)
  have hmain := isRCartierPullback_residueDifferent sX j P hj hX hdim hTv hQ hΔP hR hτ₀0 hτ₀ hρ₀
    hpb
  refine ⟨⟨_, hmain⟩, fun ΔS hΔS => ?_⟩
  obtain rfl := add_left_cancel (isRCartierPullback_eq j (hΔS τ₀ hτ₀0 hτ₀ ρ₀ hρ₀)
    (hmain τ₀ hτ₀0 hτ₀ ρ₀ hρ₀))
  -- the canonical divisors `div ρ₀` of `S` and `div τ₀` of `X`, and `K_S + Δ_S` is `ℝ`-Cartier
  have hKρ₀ := isCanonicalDivisor_divisorOfForm hTv hdimT hρ₀0
  have hK₀ := isCanonicalDivisor_divisorOfForm hX (n := n + 1) (by rw [hdim]; norm_cast) hτ₀0
  have hRC : RDivisor.IsRCartier (Divisor.toRDivisor (divisorOfForm ρ₀) +
      (QDivisor.toRDivisor BS₀ + ∑ Q ∈ Δ.support, Δ.coeff Q • QDivisor.toRDivisor (R Q))) := by
    obtain ⟨m, r, L, L', hL, -, hL', hG⟩ := hmain τ₀ hτ₀0 hτ₀ ρ₀ hρ₀
    refine ⟨m, r, L', fun i => (hL' i).2.isCartier (hL i), fun Γ => ?_⟩
    rw [hG, MMP.Flips.coeff_sum_smul_toRDivisor]
  -- `dim S ≥ 1`
  have hn1 : 1 ≤ n := by
    let _ : PartialOrder T := specializationOrder T
    have hn' : Order.krullDim T = n := by
      rw [← hdimT]
      exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := T))).symm
    have := Order.coheight_le_krullDim Q₀.genericPoint
    rw [hn', Q₀.coheight_genericPoint] at this
    exact_mod_cast this
  have hklt := pos_of_isLogDiscrepancy_realDifferent sX j P hj hX hdim hTv hdimT hQ hR hτ₀0 hτ₀
    hK₀ hρ₀ hρ₀0 hKρ₀ hpb hΔ hΔP hplt hn1
  refine ⟨isEffective_residueDifferent P hBS₀ (fun Q => (hΔ Q).1) hΔP fun Q hQP => (hR Q hQP).1,
    ⟨hTv, ⟨n, _, hKρ₀, hRC⟩, hklt⟩, fun I _ hΔI Q' =>
      exists_coeff_realDifferent_eq sX j P hj hX hdim hTv hQ hR hτ₀0 hτ₀ hK₀ hρ₀ hpb hΔ hΔP hplt
        hn1 I hΔI Q' (by linarith [hklt n _ _ (isLogDiscrepancy_ofPrimeDivisor hTv hKρ₀ hRC Q')]),
    fun A hA hAq hAΔ _ hgen AS hAS Q => coeff_isPullback_le_residueDifferent sX j P hj hQ hBS₀ hΔP
      hR A hA hAq hAΔ hgen AS hAS Q, ?monotone⟩
  case monotone =>
    exact fun sX' _ _ _ _ _ hQ' hdim' P' Δ' _ _ _ _ j' _ _ _ _ _ hj' ΔS' hΔS' p q _ _ _ _ _ hpq hpP
      hqP hpb hqb hle PW hpPW hqPW jW _ _ hjW pT qT _ _ hpT hqT G D D' hD hD' m a a' ha ha' =>
      isLogDiscrepancy_le_of_nonpositive_diagram sX hX hdim P Δ j hj _ hmain sX' hQ'.1 hdim' P' Δ'
        j' hj' ΔS' hΔS' p q hpq hpP hqP hpb hqb hle PW hpPW hqPW jW hjW pT qT hpT hqT G D D' hD
        hD' m a a' ha ha'

end MMP.RealPltAdjunction
