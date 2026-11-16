module

public import MMP.AlgebraicGeometry.MMP.ScalingProgram.NefPolytope
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativeBasepointFree
public import MMP.AlgebraicGeometry.Singularities.KltRelativeBigCore
public import MMP.AlgebraicGeometry.Singularities.GenericSurfacePlaces

/-!
# Uniform relative freeness of adjoints near a nef adjoint with a relatively big core

Let `f : Y ⟶ S` be a morphism of projective varieties over an algebraically closed field of
characteristic zero, with `Y` normal and `ℚ`-factorial and canonical divisor `K`. Let `P` be the
real convex hull of finitely many effective `ℚ`-boundaries `Γ` with `(Y, Γ)` klt, all of them
containing a fixed effective `f`-big `ℚ`-divisor `G`, and let `Δ ∈ P` be a real boundary with
`K + Δ` nef over `S`. Inside the smallest rational affine hull `W` of `Δ` there is a rational
polytope `Q ⊆ P ∩ W` containing `Δ` in its relative interior, together with an integer `b > 0`,
such that `b • D` is relatively free over `S` for every `Γ ∈ Q`, every real `c > 0` and every
Cartier divisor `D` with `c (K + Γ) = D`. Moreover every `K + Γ`, `Γ ∈ Q`, lies in the cone
spanned by finitely many Cartier divisors that are relatively semiample over `S`.

## Main results

* `MMP.Fourfold.QDivisor.IsRelativelyBig.exists_isRelativelyFreeDivisor_nsmul_of_isRelativelyNef`.

## Implementation notes

* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero, as for
  `MMP.Fourfold.QDivisor.IsRelativelyBig.exists_isKltPair_add_pullback_sub_isAmple`.
* A rational polytope is the real convex hull, in `RDivisor Y`, of a finite set of `ℚ`-divisors.
  Effectivity, being a boundary and containing `G` are convex conditions, so they are assumed
  at the vertices of `P`.
* The smallest rational affine hull of `Δ` is `MMP.Fourfold.IsInSmallestRationalAffineHull Δ`.
* `RDivisor Y` carries no topology, so "`Δ` lies in the relative interior of `Q`" is stated
  algebraically: `Δ ∈ Q` and for every `Γ ∈ Q` the segment from `Γ` through `Δ` extends a little
  beyond `Δ` inside `Q`. For a convex set in a finite-dimensional space (here the coefficient
  space of the finitely many primes in the support of the vertices) this is the relative
  interior.
* Relative freeness of a Cartier divisor `D` is `MMP.Fourfold.IsRelativelyFreeDivisor`: the
  counit `f^* f_* 𝒪_Y(D) → 𝒪_Y(D)` is surjective, which for Cartier `D` is
  `MMP.Mori.IsRelativelyFreeCartier`. A Cartier divisor `H` is relatively semiample if some
  positive multiple `p H` is relatively free.
* `K + Δ` is a real divisor; its nefness over `S` is `MMP.Flips.IsRelativelyNef`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.22, 3.24
-/

public section

open CategoryTheory AlgebraicGeometry MMP.Fourfold MMP.Mori

namespace MMP.ChainRelativeBigCoreUniformFreeness

/-! ### Divisors that are locally principal over the base -/

section LocallyPrincipal

variable {Y S : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- A divisor `E` on `Y` is *locally principal over* `f : Y ⟶ S` if every point of `S` has an
open neighbourhood `U` such that `E` has a local equation on all of `f⁻¹(U)`. -/
private def IsLocallyPrincipalOver (f : Y ⟶ S) (E : Divisor Y) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ φ : (RationalFunctions Y)ˣ, E.IsLocalEquation (f ⁻¹ᵁ U) φ

private theorem IsLocallyPrincipalOver.add {f : Y ⟶ S} {E E' : Divisor Y}
    (h : IsLocallyPrincipalOver f E) (h' : IsLocallyPrincipalOver f E') :
    IsLocallyPrincipalOver f (E + E') := fun s => by
  obtain ⟨U, hsU, φ, hφ⟩ := h s
  obtain ⟨U', hsU', ψ, hψ⟩ := h' s
  exact ⟨U ⊓ U', ⟨hsU, hsU'⟩, φ * ψ, (hφ.mono (f.preimage_mono inf_le_left)).add
    (hψ.mono (f.preimage_mono inf_le_right))⟩

private theorem IsLocallyPrincipalOver.neg {f : Y ⟶ S} {E : Divisor Y}
    (h : IsLocallyPrincipalOver f E) : IsLocallyPrincipalOver f (-E) := fun s => by
  obtain ⟨U, hsU, φ, hφ⟩ := h s
  exact ⟨U, hsU, φ⁻¹, hφ.neg⟩

private theorem isLocallyPrincipalOver_zero (f : Y ⟶ S) : IsLocallyPrincipalOver f 0 :=
  fun _ => ⟨⊤, trivial, 1, Divisor.isLocalEquation_zero _⟩

private theorem IsLocallyPrincipalOver.nsmul {f : Y ⟶ S} {E : Divisor Y}
    (h : IsLocallyPrincipalOver f E) (n : ℕ) : IsLocallyPrincipalOver f (n • E) := by
  induction n with
  | zero => simpa using isLocallyPrincipalOver_zero f
  | succ n ih => simpa [succ_nsmul] using ih.add h

private theorem IsLocallyPrincipalOver.zsmul {f : Y ⟶ S} {E : Divisor Y}
    (h : IsLocallyPrincipalOver f E) (n : ℤ) : IsLocallyPrincipalOver f (n • E) := by
  cases n with
  | ofNat n => simpa using h.nsmul n
  | negSucc n => simpa [negSucc_zsmul] using (h.nsmul (n + 1)).neg

private theorem isLocallyPrincipalOver_principalDivisor [CompactSpace Y] (f : Y ⟶ S)
    (φ : (RationalFunctions Y)ˣ) : IsLocallyPrincipalOver f (principalDivisor φ) :=
  fun _ => ⟨⊤, trivial, φ, Divisor.isLocalEquation_principalDivisor φ _⟩

private theorem IsLocallyPrincipalOver.isCartier {f : Y ⟶ S} {E : Divisor Y}
    (h : IsLocallyPrincipalOver f E) : E.IsCartier := fun y => by
  obtain ⟨U, hU, φ, hφ⟩ := h (f y)
  exact ⟨f ⁻¹ᵁ U, hU, φ, hφ⟩

/-- On an integral scheme, a rational function as a unit of `K(X)`. -/
private noncomputable def unitOfFunctionField (c : Y.functionField) (hc : c ≠ 0) :
    (RationalFunctions Y)ˣ :=
  Units.map (Pi.ringHom fun Z => (Y.presheaf.stalkSpecializes (by
      rw [specializes_iff_mem_closure, (isGenericPoint_componentGenericPoint Y Z).def]
      exact Z.2.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _) (Set.mem_univ _) :
      componentGenericPoint Y Z ⤳ genericPoint Y)).hom).toMonoidHom (Units.mk0 c hc)

private theorem ord_unitOfFunctionField (c : Y.functionField) (hc : c ≠ 0)
    (E : MMP.Mori.PrimeDivisor Y) :
    E.ord (unitOfFunctionField c hc) = Y.ord c E.genericPoint := by
  rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  congr 1
  change (Y.presheaf.stalkSpecializes _) ((Y.presheaf.stalkSpecializes _) c) = c
  rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- **The Weil divisor of a Cartier pull-back is locally principal over the base.** If `T₀'` is
the pull-back along a closed map `f` of a Cartier divisor `T₀` on `S`, its Weil divisor `w` has a
single local equation on `f⁻¹(U)` for a neighbourhood `U` of each point of `S`: the pull-back of
a fraction `s_a / s_b` presenting a local equation of `T₀` on `U`. -/
private theorem isLocallyPrincipalOver_of_isPullback [IsLocallyNoetherian S] (f : Y ⟶ S)
    (hfc : IsClosedMap f.base) {T₀ : S.CartierDivisor} {T₀' : Y.CartierDivisor} {w : Divisor Y}
    (hT : MMP.Intersection.IsPullback f T₀ T₀')
    (hw : MMP.Intersection.IsWeilDivisorOfCartier T₀' w) :
    IsLocallyPrincipalOver f w := by
  intro s
  by_cases hs : s ∈ Set.range f.base
  swap
  · refine ⟨⟨(Set.range f.base)ᶜ, (hfc.isClosed_range).isOpen_compl⟩, hs, 1, fun E hE => ?_⟩
    obtain ⟨p, -, hp⟩ := hE
    exact absurd ⟨p, rfl⟩ hp
  obtain ⟨y, rfl⟩ := hs
  obtain ⟨g, hg⟩ := MMP.Intersection.exists_isLocalEquationAt T₀ (f y)
  obtain ⟨a, b, hab, ha, hb⟩ :=
    MMP.Intersection.exists_isFraction_stalkMap_mem_nonZeroDivisors hT.1 y hg
  obtain ⟨V₀, hx₀, G₀, sa, sb, hG₀, rfl, rfl, V, hV, hxV, hfrac⟩ :=
    MMP.Intersection.exists_fraction_nhds hg hab
  have hy₀ : y ∈ f ⁻¹ᵁ V₀ := hx₀
  haveI : Nonempty (f ⁻¹ᵁ V₀) := ⟨⟨y, hy₀⟩⟩
  have gt : ∀ (p : Y) (hp : p ∈ f ⁻¹ᵁ V₀) (t : Γ(S, V₀)),
      f.stalkMap p (S.presheaf.germ V₀ (f p) hp t) = Y.presheaf.germ (f ⁻¹ᵁ V₀) p hp (f.app V₀ t) :=
    fun p hp t => Scheme.Hom.germ_stalkMap_apply f V₀ p hp t
  have hne : ∀ t : Γ(S, V₀), f.stalkMap y (S.presheaf.germ V₀ (f y) hx₀ t) ∈
      nonZeroDivisors (Y.presheaf.stalk y) → ∀ (p : Y) (hp : p ∈ f ⁻¹ᵁ V₀),
      Y.presheaf.germ (f ⁻¹ᵁ V₀) p hp (f.app V₀ t) ≠ 0 := by
    intro t ht p hp h0
    have h1 : f.app V₀ t = 0 := germ_injective_of_isIntegral Y p hp (by rw [h0, map_zero])
    rw [gt y hy₀, h1, map_zero] at ht
    exact zero_notMem_nonZeroDivisors ht
  have hna := hne sa ha
  have hnb := hne sb hb
  set c : Y.functionField :=
    Y.germToFunctionField (f ⁻¹ᵁ V₀) (f.app V₀ sa) / Y.germToFunctionField (f ⁻¹ᵁ V₀) (f.app V₀ sb)
    with hc
  have hgen : genericPoint Y ∈ f ⁻¹ᵁ V₀ :=
    ((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ V₀).isOpen).mpr ⟨y, trivial, hy₀⟩
  have hgb : Y.germToFunctionField (f ⁻¹ᵁ V₀) (f.app V₀ sb) ≠ 0 := hnb _ hgen
  have hga : Y.germToFunctionField (f ⁻¹ᵁ V₀) (f.app V₀ sa) ≠ 0 := hna _ hgen
  have hc0 : c ≠ 0 := div_ne_zero hga hgb
  refine ⟨V, hxV, unitOfFunctionField c hc0, fun E hE => ?_⟩
  have hη : E.genericPoint ∈ f ⁻¹ᵁ V :=
    MMP.Intersection.genericPoint_mem_of_support_inter_nonempty E hE
  set η := E.genericPoint
  have hη₀ : η ∈ f ⁻¹ᵁ V₀ := hV hη
  have hgE : MMP.Intersection.IsLocalEquationAt T₀ (f η)
      (S.totalQuotientSheaf.presheaf.germ V₀ (f η) hη₀ (G₀ : _)) := ⟨V₀, hη₀, G₀, hG₀, rfl⟩
  have habE := hfrac (f η) hη
  have hbE : f.stalkMap η (S.presheaf.germ V₀ (f η) hη₀ sb) ∈
      nonZeroDivisors (Y.presheaf.stalk η) := by
    rw [gt η hη₀]; exact mem_nonZeroDivisors_of_ne_zero (hnb η hη₀)
  have hu := MMP.Intersection.isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors hbE
  set g' := (hu.unit⁻¹ : (Y.totalQuotientSheaf.presheaf.stalk η)ˣ).1 *
    MMP.Intersection.stalkToTotalQuotient η (f.stalkMap η (S.presheaf.germ V₀ (f η) hη₀ sa))
  have h' : MMP.Intersection.IsFraction g' (f.stalkMap η (S.presheaf.germ V₀ (f η) hη₀ sa))
      (f.stalkMap η (S.presheaf.germ V₀ (f η) hη₀ sb)) :=
    ⟨hu, by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩
  have hloc := hT.isLocalEquationAt hgE habE h'
  rw [← MMP.Intersection.ord_eq_coeff_of_isLocalEquationAt hw E rfl hloc,
    ord_unitOfFunctionField]
  congr 1
  have h2 := congrArg (totalQuotientStalkToFunctionField η) h'.2
  rw [map_mul, MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient,
    MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient, gt η hη₀,
    gt η hη₀, Scheme.algebraMap_germ_eq_germToFunctionField,
    Scheme.algebraMap_germ_eq_germToFunctionField] at h2
  rw [hc, eq_div_iff hgb, mul_comm, h2]

end LocallyPrincipal

/-! ### Relative ampleness of `A' - T_Y` -/

section RelativelyAmple

variable {Y S : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- The restriction of a module to an open subscheme, in the two spellings of the pull-back. -/
private noncomputable def modulePullbackIsoRestrict {Z : Scheme.{0}} (U : Z.Opens)
    (F : Z.Modules) :
    (RingedSpaceModuleAdjunction.modulePullback U.ι.toLRSHom.toShHom).obj F ≅ F.restrict U.ι :=
  (Adjunction.leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction U.ι.toLRSHom.toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι)).app F ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm

/-- Adding a divisor that is locally principal over `S` to an `f`-ample Cartier divisor keeps it
`f`-ample: over a small affine open `V` of `S` the two divisorial sheaves agree on `f⁻¹(V)`. -/
private theorem isRelativelyAmple_add_of_isLocallyPrincipalOver (f : Y ⟶ S)
    {L : Divisor Y} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL) {E : Divisor Y}
    (hE : IsLocallyPrincipalOver f E) :
    (L + E).IsRelativelyAmple f (hL.add hE.isCartier) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := (hL.add hE.isCartier).isInvertibleModule_divisorialSheaf
  haveI : IsNoetherian Y := ⟨⟩
  intro s
  obtain ⟨V, hV, hsV, hamp⟩ := hLf s
  obtain ⟨U, hsU, ψ, hψ⟩ := hE s
  obtain ⟨V', hV', hsV', hV'le⟩ :=
    exists_isAffineOpen_mem_and_subset (U := V ⊓ U) (show s ∈ V ⊓ U from ⟨hsV, hsU⟩)
  have hV'V : V' ≤ V := fun z hz => (hV'le hz).1
  have hV'U : V' ≤ U := fun z hz => (hV'le hz).2
  refine ⟨V', hV', hsV', ?_⟩
  haveI : CompactSpace (f ⁻¹ᵁ V).toScheme := hamp.1
  have hc : CompactSpace (f ⁻¹ᵁ V').toScheme := inferInstance
  have hLV' : Stacks.Ample.IsAmple (f ⁻¹ᵁ V').toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V').ι L.divisorialSheaf) :=
    Stacks.RelativeAmpleComposition.isAmple_restrict_of_le (f.preimage_mono hV'V)
      L.divisorialSheaf hamp hc
  have e : (L + E).divisorialSheaf.restrict (f ⁻¹ᵁ V').ι ≅
      L.divisorialSheaf.restrict (f ⁻¹ᵁ V').ι :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).mapIso
        (Divisor.divisorialSheafMulIso ψ (D' := L + E - principalDivisor ψ) fun P => by
          rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, sub_add_cancel]) ≪≫
      Divisor.restrictDivisorialSheafIsoOfEqOn fun P hP => by
        rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
          hψ P (hP.mono (Set.inter_subset_inter_right _ (f.preimage_mono hV'U))),
          add_sub_cancel_right]
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (modulePullbackIsoRestrict _ _ ≪≫ e ≪≫ (modulePullbackIsoRestrict _ _).symm)).mpr hLV'

open Stacks.Ample in
/-- `𝒪_Y(nD) ≅ 𝒪_Y(D)^{⊗ n}` for a Cartier divisor `D`. -/
private noncomputable def divisorialSheafNsmulIso {D : Divisor Y} (hD : D.IsCartier) (n : ℕ) :
    haveI := hD.isInvertibleModule_divisorialSheaf
    (n • D).divisorialSheaf ≅ tensorPowModule Y D.divisorialSheaf (n : ℤ) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  induction n with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (tensorPowModuleZeroIso Y D.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hD.nsmul n).divisorialSheafTensorIso hD).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (tensorPowModuleOneIso Y D.divisorialSheaf).symm ≪≫
      tensorPowModuleAddIso Y D.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

/-- A positive multiple of an ample Cartier divisor is ample. -/
private theorem isAmple_nsmul {D : Divisor Y} (hD : D.IsCartier) (hA : D.IsAmple hD) {n : ℕ}
    (hn : 0 < n) : (n • D).IsAmple (hD.nsmul n) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := (hD.nsmul n).isInvertibleModule_divisorialSheaf
  unfold Divisor.IsAmple
  rw [Stacks.RelativeVeryAmple.isAmple_congr _ _ (divisorialSheafNsmulIso hD n),
    ← Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn]
  exact hA

/-- **An ample `ℚ`-divisor minus a pull-back from the base is relatively ample.** If `A` is
ample and `T ∼_ℚ c [f^*T₀]` for a Cartier divisor `T₀` on `S`, then `A - T` has an `f`-ample
Cartier multiple. -/
private theorem hasRelativelyAmpleMultiple_sub_of_qLinearlyEquivalent [IsLocallyNoetherian S]
    (f : Y ⟶ S) [QuasiCompact f] (hfc : IsClosedMap f.base) {A T : QDivisor Y} (hA : A.IsAmple)
    {c : ℚ} {T₀ : S.CartierDivisor} {T₀' : Y.CartierDivisor} {w : Divisor Y}
    (hT : MMP.Intersection.IsPullback f T₀ T₀')
    (hw : MMP.Intersection.IsWeilDivisorOfCartier T₀' w)
    (hlin : T.QLinearlyEquivalent (c • Divisor.toQDivisor w)) :
    (A - T).HasRelativelyAmpleMultiple f := by
  obtain ⟨m₁, hm₁, D₁, hD₁, hD₁c, hD₁a⟩ := hA
  obtain ⟨m₂, hm₂, φ, hφ⟩ := hlin
  have hwp := isLocallyPrincipalOver_of_isPullback f hfc hT hw
  set q : ℕ := m₂ * c.den
  have hq : 0 < q := Nat.mul_pos hm₂ c.den_pos
  set E : Divisor Y := (-((m₁ : ℤ) * m₂ * c.num)) • w + (-((m₁ : ℤ) * c.den)) • principalDivisor φ
  have hE : IsLocallyPrincipalOver f E :=
    (hwp.zsmul _).add ((isLocallyPrincipalOver_principalDivisor f φ).zsmul _)
  have hqD := hD₁c.nsmul q
  refine ⟨m₁ * q, Nat.mul_pos hm₁ hq, q • D₁ + E, hqD.add hE.isCartier, ?_,
    isRelativelyAmple_add_of_isLocallyPrincipalOver f hqD
      (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple_divisorialSheaf f hqD
        (isAmple_nsmul hD₁c hD₁a hq)) hE⟩
  refine DivisorWithCoeffs.ext' fun P => ?_
  have h1 := congrArg (fun F : QDivisor Y => F.coeff P) hD₁
  have h2 := congrArg (fun F : QDivisor Y => F.coeff P) hφ
  have hc : (c.num : ℚ) = c * c.den := by rw [Rat.mul_den_eq_num]
  simp only [E, q, map_add, map_zsmul, map_nsmul, DivisorWithCoeffs.coeff_add,
    DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
    smul_eq_mul, zsmul_eq_mul, nsmul_eq_mul, coeff_principalDivisor] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  linear_combination ((m₂ : ℚ) * c.den) * h1 + ((m₁ : ℚ) * c.den) * h2 -
    ((m₁ : ℚ) * m₂ * w.coeff P) * hc

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-nef. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple {k : Type} [Field k]
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] {f : Y ⟶ S} {D : QDivisor Y}
    (h : D.HasRelativelyAmpleMultiple f) : D.IsRelativelyNef sY f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have hq : D.IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩
  refine ⟨hq, fun C hC => ?_⟩
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp)]
  set F : Divisor Y := (D.cartierIndexSMul hq : Divisor Y)
  have hFc : F.IsCartier := (D.cartierIndexSMul hq).2
  set N := D.cartierIndex hq
  have hLpos : 0 < L.degreeOn k sY C.ι C.dim_le hL := by
    have := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      L.divisorialSheaf hamp C hC
  have hFL : m • F = N • L := by
    apply Divisor.toQDivisor_injective
    rw [map_nsmul, map_nsmul, QDivisor.toQDivisor_cartierIndexSMul, hLD, ← natCast_zsmul,
      ← natCast_zsmul, smul_smul, smul_smul, mul_comm]
  have key : (m : ℤ) * F.degreeOn k sY C.ι C.dim_le hFc =
      N * L.degreeOn k sY C.ι C.dim_le hL := by
    rw [← Divisor.degreeOn_nsmul', ← Divisor.degreeOn_nsmul', Divisor.degreeOn_congr hFL]
  have hFpos : 0 ≤ F.degreeOn k sY C.ι C.dim_le hFc :=
    nonneg_of_mul_nonneg_right (a := (m : ℤ)) (by rw [key]; positivity) (by exact_mod_cast hm)
  exact mul_nonneg (by positivity) (by exact_mod_cast hFpos)

open MonoidalCategory in
/-- If `𝒪_Y(D₀) ≅ 𝒪_Y(Ec)` then `𝒪_Y(m • Ec) ≅ 𝒪_Y(m • D₀)` for `m ≥ 1`. -/
private theorem nonempty_sheaf_nsmul_iso {D₀ : Divisor Y} (hD₀ : D₀.IsCartier)
    {Ec : Y.CartierDivisor}
    (e : D₀.divisorialSheaf ≅ MMP.CartierDivisor.sheaf Ec) (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (MMP.CartierDivisor.sheaf (m • Ec) ≅
      (m • D₀).divisorialSheaf) ∧ (m • D₀).IsCartier := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [one_nsmul, one_nsmul]
    exact ⟨⟨e.symm⟩, hD₀⟩
  | succ n hn ih =>
    obtain ⟨⟨ie⟩, hc⟩ := ih
    rw [succ_nsmul, succ_nsmul]
    refine ⟨⟨?_⟩, hc.add hD₀⟩
    exact (MMP.CartierDivisorSheaf.sheafMulIso (n • Ec) Ec).symm ≪≫
      MonoidalCategory.tensorIso ie e.symm ≪≫ hc.divisorialSheafTensorIso hD₀

/-- **A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-big.** -/
private theorem isRelativelyBig_of_hasRelativelyAmpleMultiple {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sS]
    (f : Y ⟶ S) (hf : f ≫ sS = sY) {D : QDivisor Y} (h : D.HasRelativelyAmpleMultiple f) :
    D.IsRelativelyBig f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  haveI := hL.isInvertibleModule_divisorialSheaf
  obtain ⟨Ec, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L.divisorialSheaf
  have hA : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf Ec) := by
    intro s
    obtain ⟨V, hV, hsV, hampV⟩ := hamp s
    exact ⟨V, hV, hsV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
      ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1
        hampV⟩
  have hbig : IsRelativelyBigCartier f Ec :=
    (MMP.Mori.isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sY sS f hf Ec).2
      ⟨1, one_pos, Ec, 0, hA, MMP.Intersection.isEffective_zero, by
        rw [one_smul, add_zero]⟩
  refine ⟨m, hm, L, by rw [hLD]; norm_cast, hL, ?_⟩
  obtain ⟨a, b, ha, hb, c, hc, k₀, hk⟩ := hbig
  refine ⟨a, b, ha, hb, c, hc, max k₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hk0 : k₀ ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨n, rfl⟩ : ∃ n' : ℕ, n = (n' : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  obtain ⟨⟨ie⟩, -⟩ := nonempty_sheaf_nsmul_iso hL e n (by omega)
  have h := hk _ hk0
  rw [natCast_zsmul] at h ⊢
  rwa [relativeGenericRank, ← Scheme.Modules.fiberRank_eq_of_iso
    ((Scheme.Modules.pushforward f).mapIso ie)]

end RelativelyAmple

/-! ### Relative nefness in the two senses -/

section Nef

variable {k : Type} [Field k] {Y S : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY]
  [IsLocallyNoetherian Y] [IsNormal Y]

/-- Every Cartier divisor has an intersection number with a proper curve: the normalization of
the curve is a normal proper curve birational to it. -/
private theorem exists_isCartierIntersectionNumber (C : ProperCurve sY) (L : Divisor Y)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sY C L hL d := by
  let p := C.ι ≫ sY
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV
          hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- A Cartier divisor that is `f`-nef as a real divisor is `f`-nef as a `ℚ`-divisor. -/
private theorem isRelativelyNef_toQDivisor_of_isRelativelyNef {f : Y ⟶ S} {H : Divisor Y}
    (hH : H.IsCartier) (h : MMP.Flips.IsRelativelyNef k sY f (Divisor.toRDivisor H)) :
    (Divisor.toQDivisor H).IsRelativelyNef sY f := by
  obtain ⟨m, r, L, hL, hDeq, hnn⟩ := h
  have hq := QDivisor.isQCartier_toQDivisor hH
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sY hq fun C hC => ?_
  choose d hd using fun j => exists_isCartierIntersectionNumber C (L j) (hL j)
  obtain ⟨d', hd'⟩ := exists_isCartierIntersectionNumber C H hH
  have hx := hnn C hC _ ⟨hL, d, hDeq, hd, rfl⟩
  have hy : MMP.Flips.IsRIntersectionNumber k sY (Divisor.toRDivisor H)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ => H) C (∑ _j : Fin 1, (1 : ℝ) * d') :=
    ⟨fun _ => hH, fun _ => d', by simp, fun _ => hd', rfl⟩
  have heq := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sY C).1 _ r L _ _ _ _
    ⟨hL, d, hDeq, hd, rfl⟩ hy
  rw [heq] at hx
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul] at hx
  rw [QDivisor.intersectionNumber_toQDivisor k sY C.ι C.dim_le H hH hq,
    ← MMP.Fourfold.Oai4C1.Negativity.eq_degreeOn_of_isCartierIntersectionNumber hd']
  exact_mod_cast hx

/-- A nonnegative multiple of an `f`-nef real divisor is `f`-nef. -/
private theorem isRelativelyNef_smul {f : Y ⟶ S} {D : RDivisor Y}
    (h : MMP.Flips.IsRelativelyNef k sY f D) {a : ℝ} (ha : 0 ≤ a) :
    MMP.Flips.IsRelativelyNef k sY f (a • D) := by
  obtain ⟨m, r, L, hL, hD, hnn⟩ := h
  refine ⟨m, a • r, L, hL, by rw [hD, Finset.smul_sum]; simp [smul_smul], fun C hC x hx => ?_⟩
  obtain ⟨hL', d, -, hd, rfl⟩ := hx
  have := hnn C hC _ ⟨hL', d, hD, hd, rfl⟩
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  exact mul_nonneg ha this

end Nef

/-! ### Rational polytopes along the smallest rational affine hull -/

section Polytope

open Set

/-- The standard simplex is a rational polyhedron. -/
private theorem isRationalPolyhedron_stdSimplex (r : ℕ) :
    IsRationalPolyhedron (stdSimplex ℝ (Fin r)) := by
  classical
  have hsingle : ∀ (i : Fin r) (x : Fin r → ℝ),
      ratAffineForm (Pi.single i 1, 0) x = x i := fun i x => by
    simp only [ratAffineForm]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp
  refine ⟨{(fun _ => 1, -1)}, Finset.univ.image (fun i => (Pi.single i 1, 0)), ?_⟩
  ext x
  simp only [stdSimplex, mem_setOf_eq, Finset.mem_singleton, forall_eq, Finset.mem_image,
    Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff, hsingle]
  simp only [ratAffineForm, Rat.cast_one, one_mul, Rat.cast_neg]
  constructor
  · rintro ⟨h0, h1⟩; exact ⟨by rw [h1]; ring, h0⟩
  · rintro ⟨h1, h0⟩; exact ⟨h0, by linarith⟩

/-- A rational parallelotope is the convex hull of finitely many rational points (its corners). -/
private theorem IsRationalParallelotope.exists_finset {r : ℕ} {Q : Set (Fin r → ℝ)}
    (hQ : IsRationalParallelotope Q) :
    ∃ V : Finset (Fin r → ℚ),
      Q = convexHull ℝ ((fun v i => (v i : ℝ)) '' (V : Set (Fin r → ℚ))) := by
  classical
  obtain ⟨d, p, e, a, b, -, hab, rfl⟩ := hQ
  let φ : (Fin d → ℝ) →ᵃ[ℝ] (Fin r → ℝ) :=
    (Fintype.linearCombination ℝ (fun i j => (e i j : ℝ))).toAffineMap +
      AffineMap.const ℝ _ (fun j => (p j : ℝ))
  have hφ : ∀ s j, φ s j = (p j : ℝ) + ∑ i, s i * (e i j : ℝ) := fun s j => by
    simp [φ, Fintype.linearCombination_apply, add_comm]
  let corner : (Fin d → Bool) → Fin r → ℚ :=
    fun c j => p j + ∑ i, (if c i then b i else a i) * e i j
  let C : Set (Fin d → ℝ) := univ.pi fun i => {(a i : ℝ), (b i : ℝ)}
  refine ⟨Finset.univ.image corner, ?_⟩
  have hbox : (univ.pi fun i => Icc (a i : ℝ) (b i)) = convexHull ℝ C := by
    rw [convexHull_pi]
    refine pi_congr rfl fun i _ => ?_
    rw [convexHull_pair, segment_eq_Icc (by exact_mod_cast (hab i).le)]
  have hV : (fun v i => (v i : ℝ)) '' ((Finset.univ.image corner : Finset _) :
      Set (Fin r → ℚ)) = φ '' C := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, image_univ, mem_image, mem_range]
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨fun i => ((if c i then b i else a i : ℚ) : ℝ), fun i _ => ?_, ?_⟩
      · by_cases h : c i <;> simp [h]
      · funext j
        rw [hφ]
        simp only [corner]
        push_cast
        exact congrArg _ (Finset.sum_congr rfl fun i _ => by by_cases h : c i <;> simp [h])
    · rintro ⟨s, hs, rfl⟩
      have hs' : ∀ i, s i = ((if decide (s i = b i) then b i else a i : ℚ) : ℝ) := fun i => by
        rcases hs i (mem_univ i) with h | h <;> by_cases h' : s i = b i <;> simp_all
      refine ⟨corner fun i => decide (s i = b i), ⟨_, rfl⟩, ?_⟩
      funext j; rw [hφ]; simp only [corner]; push_cast
      exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [← hs' i])
  rw [hV, ← AffineMap.image_convexHull, ← hbox]
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, Set.mem_univ_pi.2 hs, funext fun j => hφ s j⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, Set.mem_univ_pi.1 hs, funext fun j => hφ s j⟩

/-- From a point `x` of the relative interior of `Q`, the segment from any `y ∈ Q` through `x`
extends a little beyond `x` inside `Q`. -/
private theorem exists_add_smul_sub_mem_of_mem_intrinsicInterior {r : ℕ} {Q : Set (Fin r → ℝ)}
    {x y : Fin r → ℝ} (hx : x ∈ intrinsicInterior ℝ Q) (hy : y ∈ Q) :
    ∃ ε : ℝ, 0 < ε ∧ x + ε • (x - y) ∈ Q := by
  obtain ⟨z, hz, rfl⟩ := mem_intrinsicInterior.1 hx
  have hyA : y ∈ affineSpan ℝ Q := subset_affineSpan ℝ Q hy
  let g : ℝ → affineSpan ℝ Q := fun t =>
    ⟨t • ((z : Fin r → ℝ) - y) + z, by
      simpa using (affineSpan ℝ Q).smul_vsub_vadd_mem t z.2 hyA z.2⟩
  have hg : Continuous g := Continuous.subtype_mk (by fun_prop) _
  have hg0 : g 0 = z := Subtype.ext (by simp [g])
  have hmem : g ⁻¹' interior ((↑) ⁻¹' Q) ∈ nhds (0 : ℝ) :=
    hg.continuousAt.preimage_mem_nhds (hg0 ▸ isOpen_interior.mem_nhds hz)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have h := interior_subset (hball (show δ / 2 ∈ Metric.ball (0 : ℝ) δ by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith))
  have : ((g (δ / 2) : affineSpan ℝ Q) : Fin r → ℝ) = (z : Fin r → ℝ) + (δ / 2) • (↑z - y) :=
    add_comm _ _
  rw [← this]
  exact h

variable {Y : Scheme.{0}}

private theorem toRDivisor_qsmul (q : ℚ) (D : QDivisor Y) :
    QDivisor.toRDivisor (q • D) = (q : ℝ) • QDivisor.toRDivisor D :=
  DivisorWithCoeffs.ext' fun P => by simp [DivisorWithCoeffs.coeff_smul]

private theorem coeff_sum_smul {ι : Type*} (s : Finset ι) (μ : ι → ℝ) (D : ι → RDivisor Y)
    (P : MMP.Mori.PrimeDivisor Y) :
    (∑ i ∈ s, μ i • D i).coeff P = ∑ i ∈ s, μ i * (D i).coeff P := by
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul]

/-- **A rational polytope around a point of a rational polytope, along its smallest rational
affine hull.** If `Δ` lies in the real convex hull of finitely many `ℚ`-divisors `V`, there is a
finite set `VQ` of `ℚ`-divisors whose convex hull lies in that of `V` and in the smallest
rational affine hull of `Δ`, and contains `Δ` in its relative interior. -/
private theorem exists_finset_rationalPolytope (V : Finset (QDivisor Y)) {Δ : RDivisor Y}
    (hΔ : Δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor Y)))) :
    ∃ VQ : Finset (QDivisor Y),
      convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) ⊆
          convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor Y))) ∧
      (∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))),
          IsInSmallestRationalAffineHull Δ Γ) ∧
      Δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) ∧
      ∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))), ∃ ε : ℝ, 0 < ε ∧
          Δ + ε • (Δ - Γ) ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) := by
  classical
  set r := V.card
  let e : Fin r → QDivisor Y := fun i => (V.equivFin.symm i).1
  have he : Set.range e = V := by
    ext D
    constructor
    · rintro ⟨i, rfl⟩; exact (V.equivFin.symm i).2
    · intro hD; exact ⟨V.equivFin ⟨D, hD⟩, by simp [e]⟩
  let φ : (Fin r → ℝ) →ₗ[ℝ] RDivisor Y :=
    Fintype.linearCombination ℝ (fun i => QDivisor.toRDivisor (e i))
  have hφ : ∀ μ, φ μ = ∑ i, μ i • QDivisor.toRDivisor (e i) := fun μ =>
    Fintype.linearCombination_apply _ _ _
  have hcoeff : ∀ μ P, (φ μ).coeff P = ∑ i, μ i * ((e i).coeff P : ℝ) := fun μ P => by
    rw [hφ, coeff_sum_smul]; rfl
  have hhull : convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor Y))) =
      φ '' stdSimplex ℝ (Fin r) := by
    rw [← convexHull_rangle_single_eq_stdSimplex, LinearMap.image_convexHull, ← he,
      ← Set.range_comp, ← Set.range_comp]
    congr 2
    funext i
    simp [hφ, Pi.single_apply]
  rw [hhull] at hΔ
  obtain ⟨l₀, hlN, rfl⟩ := hΔ
  obtain ⟨Q, hQ, hQN, hlQ, -⟩ := exists_rationalParallelotope (isRationalPolyhedron_stdSimplex r)
    hlN
  obtain ⟨Vc, hVc⟩ := IsRationalParallelotope.exists_finset hQ
  refine ⟨Vc.image (fun v => ∑ i, v i • e i), ?_⟩
  have hconv : convexHull ℝ (QDivisor.toRDivisor ''
      ((Vc.image (fun v => ∑ i, v i • e i) : Finset (QDivisor Y)) : Set (QDivisor Y))) =
      φ '' Q := by
    rw [hVc, LinearMap.image_convexHull, Finset.coe_image, ← Set.image_comp, ← Set.image_comp]
    congr 2
    funext v
    simp only [Function.comp_apply, map_sum, toRDivisor_qsmul, hφ]
  rw [hconv]
  have hlQ' : l₀ ∈ Q := intrinsicInterior_subset hlQ
  refine ⟨(Set.image_mono fun x hx => (hQN hx).1).trans (hhull ▸ le_rfl), ?_,
    ⟨l₀, hlQ', rfl⟩, ?_⟩
  · rintro _ ⟨μ, hμQ, rfl⟩
    have hμW := (hQN hμQ).2
    rw [SetLike.mem_coe, mem_rationalAffineHull] at hμW
    refine ⟨fun P hP => ?_, fun c q hcq => ?_⟩
    · rw [Finsupp.mem_support_iff] at hP ⊢
      intro h0
      apply hP
      have := hμW (fun i => (e i).coeff P, 0) (by
        simp only [ratAffineForm, Rat.cast_zero, add_zero]
        rw [← DivisorWithCoeffs.coeff_apply, hcoeff] at h0
        rw [← h0]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
      simp only [ratAffineForm, Rat.cast_zero, add_zero] at this
      rw [← DivisorWithCoeffs.coeff_apply, hcoeff, ← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · have key : ∀ ν : Fin r → ℝ, (c.sum fun P cP => (cP : ℝ) * (φ ν).coeff P) =
          ratAffineForm (fun i => c.sum fun P cP => cP * (e i).coeff P, -q) ν + q := by
        intro ν
        simp only [ratAffineForm, Rat.cast_neg, neg_add_cancel_right, Finsupp.sum, hcoeff,
          Finset.mul_sum, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun i _ => by ring
      have h0 := hμW (fun i => c.sum fun P cP => cP * (e i).coeff P, -q) (by
        have := key l₀; rw [hcq] at this; linarith)
      rw [key μ, h0, zero_add]
  · rintro _ ⟨μ, hμQ, rfl⟩
    obtain ⟨ε, hε, hmem⟩ := exists_add_smul_sub_mem_of_mem_intrinsicInterior hlQ hμQ
    exact ⟨ε, hε, ⟨_, hmem, by simp [map_add, map_smul, map_sub]⟩⟩

end Polytope

end MMP.ChainRelativeBigCoreUniformFreeness

namespace MMP.Fourfold

open MMP.Mori

open scoped Pointwise in
open MMP.ChainRelativeBigCoreUniformFreeness in
/-- **Uniform relative freeness near a nef adjoint with a relatively big core.** Let
`f : Y ⟶ S` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, with `Y` normal and `ℚ`-factorial and `K` a canonical divisor of `Y`. Let
`V` be a finite set of effective `ℚ`-boundaries `Γ` with `(Y, Γ)` klt and `G ≤ Γ`, where `G` is
an effective `f`-big `ℚ`-divisor, and let `Δ` be a real divisor in the convex hull of `V` with
`K + Δ` nef over `S`. Then there is a finite set `VQ` of `ℚ`-divisors whose convex hull `Q` lies
in that of `V` and in the smallest rational affine hull of `Δ` and contains `Δ` in its relative
interior, and an integer `b > 0`, such that `b • D` is relatively free over `S` for every
`Γ ∈ Q`, every real `c > 0` and every Cartier divisor `D` with `c • (K + Γ) = D`; and there is a
finite set `H` of Cartier divisors, each with a relatively free positive multiple, such that
every `K + Γ` with `Γ ∈ Q` is a nonnegative real combination of the members of `H`. -/
@[mmp "prop_fourfold_relative_big_core_uniform_freeness"]
public theorem QDivisor.IsRelativelyBig.exists_isRelativelyFreeDivisor_nsmul_of_isRelativelyNef
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y S : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sS]
    [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (hY : IsQFactorial sY)
    (f : Y ⟶ S) (hf : f ≫ sS = sY) {K : Divisor Y} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n)
    {G : QDivisor Y} (hG : G.IsRelativelyBig f) (hG₀ : G.IsEffective)
    (V : Finset (QDivisor Y)) (hVeff : ∀ Γ ∈ V, Γ.IsEffective)
    (hV₁ : ∀ Γ ∈ V, ∀ E, Γ.coeff E ≤ 1) (hVG : ∀ Γ ∈ V, G ≤ Γ)
    (hVklt : ∀ Γ ∈ V, IsKltPair sY Γ) {Δ : RDivisor Y}
    (hΔ : Δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor Y))))
    (hnef : MMP.Flips.IsRelativelyNef k sY f (Divisor.toRDivisor K + Δ)) :
    ∃ VQ : Finset (QDivisor Y),
      convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) ⊆
          convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor Y))) ∧
      (∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))),
          IsInSmallestRationalAffineHull Δ Γ) ∧
      Δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) ∧
      (∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))), ∃ ε : ℝ, 0 < ε ∧
          Δ + ε • (Δ - Γ) ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y)))) ∧
      (∃ b : ℕ, 0 < b ∧
        ∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))), ∀ c : ℝ, 0 < c →
          ∀ D : Divisor Y, D.IsCartier → c • (Divisor.toRDivisor K + Γ) = Divisor.toRDivisor D →
            IsRelativelyFreeDivisor f ((b : ℤ) • D)) ∧
      ∃ H : Finset (Divisor Y),
        (∀ h ∈ H, h.IsCartier ∧ ∃ p : ℕ, 0 < p ∧ IsRelativelyFreeDivisor f ((p : ℤ) • h)) ∧
        ∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))),
          ∃ t : Divisor Y → ℝ, (∀ h, 0 ≤ t h) ∧
            Divisor.toRDivisor K + Γ = ∑ h ∈ H, t h • Divisor.toRDivisor h := by
  classical
  obtain ⟨n, hKn⟩ := hK
  haveI : IsIntegral S := (inferInstance : AlgebraicGeometry.IsVariety k sS).toIsIntegral
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  haveI : IsProper sY := inferInstance
  haveI : IsProper (f ≫ sS) := by rw [hf]; infer_instance
  haveI : IsProper f := IsProper.of_comp f sS
  have hfc : IsClosedMap f.base := f.isClosedMap
  have hset : IsProjectiveSetting k sY sS f :=
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, hf⟩
  have hQC := MMP.Fourfold.isQCartier_of_isQFactorial sY hY
  obtain ⟨A', TY, hA', -, ⟨c, T₀, T₀', w, hT, hw, hTlin⟩, -, hCklt⟩ :=
    QDivisor.IsRelativelyBig.exists_isKltPair_add_pullback_sub_isAmple sY sS hY f hf hG hG₀ V
      hVeff hVG hVklt
  have hAf : (A' - TY).HasRelativelyAmpleMultiple f :=
    hasRelativelyAmpleMultiple_sub_of_qLinearlyEquivalent f hfc hA' hT hw hTlin
  have hAnef : (A' - TY).IsRelativelyNef sY f := isRelativelyNef_of_hasRelativelyAmpleMultiple hAf
  have hAbig : (A' - TY).IsRelativelyBig f :=
    isRelativelyBig_of_hasRelativelyAmpleMultiple sY sS f hf hAf
  set τ : QDivisor Y := TY - A' with hτ
  let B : V → QDivisor Y := fun Γ => Γ.1 + τ
  have hBklt : ∀ j, IsKltPair sY (B j) := fun j => by
    simpa [B, hτ, add_sub_assoc] using (hCklt j.1 j.2).1
  have hB1 : ∀ j P, (B j).coeff P ≤ 1 := fun j P => by
    have h := (MMP.Fourfold.isKltPair_iff_mori_isKltPair sY hKn (hBklt j).1).1 (hBklt j)
    exact (roundDown_nonpos_iff.mp h.2.2 P).le
  obtain ⟨-, -, VN', hVN'⟩ := exists_finset_rationalAffine_nefRegion_eq_of_isKltPair sY sS f hset
    hY ⟨n, hKn⟩ (hQC (A' - TY)) hAf B hB1 hBklt
  have hKτ : QDivisor.toRDivisor (Divisor.toQDivisor K + (A' - TY)) + QDivisor.toRDivisor τ =
      Divisor.toRDivisor K := by
    rw [← map_add, hτ, add_assoc, sub_add_sub_cancel, sub_self, add_zero,
      QDivisor.toRDivisor_toQDivisor]
  have hrangeB : Set.range (fun j => QDivisor.toRDivisor (B j)) =
      QDivisor.toRDivisor τ +ᵥ QDivisor.toRDivisor '' (V : Set (QDivisor Y)) := by
    ext D
    simp only [Set.mem_range, Set.mem_vadd_set, Set.mem_image, B, map_add, vadd_eq_add,
      Subtype.exists, Finset.mem_coe]
    constructor
    · rintro ⟨Γ, hΓ, rfl⟩; exact ⟨_, ⟨Γ, hΓ, rfl⟩, add_comm _ _⟩
    · rintro ⟨_, ⟨Γ, hΓ, rfl⟩, rfl⟩; exact ⟨Γ, hΓ, add_comm _ _⟩
  set VN : Finset (QDivisor Y) := VN'.image (fun v => v - τ)
  have hVN : QDivisor.toRDivisor '' (VN' : Set (QDivisor Y)) =
      QDivisor.toRDivisor τ +ᵥ QDivisor.toRDivisor '' (VN : Set (QDivisor Y)) := by
    ext D
    simp only [VN, Set.mem_vadd_set, Set.mem_image, Finset.coe_image, vadd_eq_add,
      Finset.mem_coe, exists_exists_and_eq_and, map_sub]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, by abel⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, by abel⟩
  have hnefR : ∀ Γ : RDivisor Y, Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VN : Set _)) ↔
      Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor Y))) ∧
        MMP.Flips.IsRelativelyNef k sY f (Divisor.toRDivisor K + Γ) := by
    intro Γ
    have h := Set.ext_iff.mp hVN' (QDivisor.toRDivisor τ + Γ)
    have e1 : QDivisor.toRDivisor τ + Γ ∈
        convexHull ℝ (QDivisor.toRDivisor '' (VN' : Set (QDivisor Y))) ↔
        Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VN : Set (QDivisor Y))) := by
      rw [hVN, convexHull_vadd, ← vadd_eq_add (QDivisor.toRDivisor τ) Γ,
        Set.vadd_mem_vadd_set_iff]
    have e2 : QDivisor.toRDivisor τ + Γ ∈
        convexHull ℝ (Set.range fun j => QDivisor.toRDivisor (B j)) ↔
        Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor Y))) := by
      rw [hrangeB, convexHull_vadd, ← vadd_eq_add (QDivisor.toRDivisor τ) Γ,
        Set.vadd_mem_vadd_set_iff]
    have e3 : QDivisor.toRDivisor (Divisor.toQDivisor K + (A' - TY)) +
        (QDivisor.toRDivisor τ + Γ) = Divisor.toRDivisor K + Γ := by
      rw [← add_assoc, hKτ]
    rw [← e1, ← h, Set.mem_setOf_eq, e2, e3]
  obtain ⟨VQ, hQsub, hQhull, hΔQ, hQint⟩ :=
    exists_finset_rationalPolytope VN ((hnefR Δ).2 ⟨hΔ, hnef⟩)
  have hQV : convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) ⊆
      convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor Y))) :=
    fun Γ hΓ => ((hnefR Γ).1 (hQsub hΓ)).1
  have hQnef : ∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))),
      MMP.Flips.IsRelativelyNef k sY f (Divisor.toRDivisor K + Γ) :=
    fun Γ hΓ => ((hnefR Γ).1 (hQsub hΓ)).2
  have hmul : ∀ v : QDivisor Y, ∃ m : ℕ, 0 < m ∧ ∃ H : Divisor Y,
      Divisor.toQDivisor H = (m : ℤ) • (Divisor.toQDivisor K + v) ∧ H.IsCartier := fun v => by
    obtain ⟨m, hm, H, hH, hHc⟩ := (hQC (Divisor.toQDivisor K + v)).exists_pos
    exact ⟨m, hm, H, hH, hHc⟩
  choose m hm H hHeq hHc using hmul
  have hHR : ∀ v, Divisor.toRDivisor (H v) =
      (m v : ℝ) • (Divisor.toRDivisor K + QDivisor.toRDivisor v) := fun v => by
    refine DivisorWithCoeffs.ext' fun P => ?_
    have h := congrArg (fun F : QDivisor Y => F.coeff P) (hHeq v)
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      zsmul_eq_mul] at h
    simp only [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, QDivisor.coeff_toRDivisor, smul_eq_mul]
    have h' := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at h'
    exact h'
  have hfree : ∀ v ∈ VQ, ∃ p : ℕ, 0 < p ∧ IsRelativelyFreeDivisor f ((p : ℤ) • H v) := by
    intro v hv
    have hvQ : QDivisor.toRDivisor v ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set _)) :=
      subset_convexHull ℝ _ ⟨v, hv, rfl⟩
    have hHnef : (Divisor.toQDivisor (H v)).IsRelativelyNef sY f :=
      isRelativelyNef_toQDivisor_of_isRelativelyNef (hHc v)
        (by rw [hHR]; exact isRelativelyNef_smul (hQnef _ hvQ) (Nat.cast_nonneg _))
    have hCmem : QDivisor.toRDivisor (v + τ) ∈
        convexHull ℝ (QDivisor.toRDivisor '' Set.range B) := by
      rw [← Set.range_comp]
      change QDivisor.toRDivisor (v + τ) ∈
        convexHull ℝ (Set.range fun j => QDivisor.toRDivisor (B j))
      rw [hrangeB, convexHull_vadd, map_add, add_comm, ← vadd_eq_add,
        Set.vadd_mem_vadd_set_iff]
      exact hQV hvQ
    have hCklt : IsKltPair sY (v + τ) :=
      MMP.Fourfold.isKltPair_of_mem_convexHull sY (S := Set.range B)
        (by rintro _ ⟨j, rfl⟩; exact hBklt j) hCmem ⟨hY.1, n, K, hKn, hQC _⟩
    have hCmori := (MMP.Fourfold.isKltPair_iff_mori_isKltPair sY hKn hCklt.1).1 hCklt
    have key : ((1 : ℚ) / m v) • Divisor.toQDivisor (H v) - Divisor.toQDivisor K - (v + τ) =
        A' - TY := by
      rw [hHeq v]
      have hm0 : (m v : ℚ) ≠ 0 := by exact_mod_cast (hm v).ne'
      refine DivisorWithCoeffs.ext' fun P => ?_
      simp only [hτ, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul, zsmul_eq_mul, Divisor.coeff_toQDivisor]
      push_cast
      field_simp
      ring
    obtain ⟨b₀, hb₀⟩ := MMP.Mori.exists_forall_ge_isRelativelyFreeDivisor_of_isKltPair hset
      hCmori hCklt.1.nonneg (hHc v) hHnef
      (by have := hm v; positivity : (0 : ℚ) < 1 / m v) (by rw [key]; exact hAnef)
      (by rw [key]; exact hAbig)
    exact ⟨b₀ + 1, Nat.succ_pos _, hb₀ _ (Nat.le_succ _)⟩
  set Hs : Finset (Divisor Y) := VQ.image H
  have hcone : ∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))),
      ∃ t : Divisor Y → ℝ, (∀ h, 0 ≤ t h) ∧
        Divisor.toRDivisor K + Γ = ∑ h ∈ Hs, t h • Divisor.toRDivisor h := by
    intro Γ hΓ
    obtain ⟨ι, _, μ, z, hμ0, hμ1, hz, rfl⟩ := mem_convexHull_iff_exists_fintype.mp hΓ
    choose u huV huz using hz
    refine ⟨fun h => ∑ i ∈ Finset.univ.filter (fun i => H (u i) = h), μ i / m (u i),
      fun h => Finset.sum_nonneg fun i _ => div_nonneg (hμ0 i) (Nat.cast_nonneg _), ?_⟩
    have hfib : ∑ h ∈ Hs, (∑ i ∈ Finset.univ.filter (fun i => H (u i) = h), μ i / m (u i)) •
        Divisor.toRDivisor h = ∑ i, (μ i / m (u i)) • Divisor.toRDivisor (H (u i)) := by
      simp_rw [Finset.sum_smul]
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Hs)
        (g := fun i => H (u i)) (fun i _ => Finset.mem_image_of_mem H (huV i))]
      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    rw [hfib]
    have hK1 : Divisor.toRDivisor K = ∑ i, μ i • Divisor.toRDivisor K := by
      rw [← Finset.sum_smul, hμ1, one_smul]
    rw [hK1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← huz i, hHR, smul_smul, div_mul_cancel₀ _ (by exact_mod_cast (hm (u i)).ne'), smul_add]
  obtain ⟨b, hb, hbfree⟩ := exists_pos_isRelativelyFreeDivisor_nsmul_of_mem_cone hY.1
    (inferInstance : MMP.Mori.IsVariety k sS) f hf (fun h : Hs => h.1)
    (fun h => by obtain ⟨v, -, hv⟩ := Finset.mem_image.mp h.2; rw [← hv]; exact hHc v)
    (fun h => by obtain ⟨v, hv, hvh⟩ := Finset.mem_image.mp h.2; rw [← hvh]; exact hfree v hv)
    (Hs.biUnion fun h => h.support)
    (fun h P hP => Finset.mem_biUnion.mpr ⟨h.1, h.2, hP⟩)
  refine ⟨VQ, hQV, hQhull, hΔQ, hQint, ⟨b, hb, fun Γ hΓ c hc D hD hcD => hbfree D hD ?_ ?_⟩,
    Hs, fun h hh => ?_, hcone⟩
  · obtain ⟨t, -, ht⟩ := hcone Γ hΓ
    intro P hP
    rw [Finsupp.mem_support_iff] at hP
    by_contra hPs
    apply hP
    have h1 := congrArg (fun F : RDivisor Y => F.coeff P) hcD
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul, ht,
      coeff_sum_smul] at h1
    rw [Finset.sum_eq_zero fun h hh => by
      have h0 : h.coeff P = 0 := by
        rw [DivisorWithCoeffs.coeff_apply]
        exact Finsupp.notMem_support_iff.mp fun hPh => hPs (Finset.mem_biUnion.mpr ⟨h, hh, hPh⟩)
      simp [h0], mul_zero] at h1
    exact_mod_cast h1.symm
  · obtain ⟨t, ht0, ht⟩ := hcone Γ hΓ
    refine ⟨fun h => c * t h.1, fun h => mul_nonneg hc.le (ht0 _), ?_⟩
    rw [← hcD, ht, Finset.smul_sum, ← Finset.sum_coe_sort Hs]
    exact Finset.sum_congr rfl fun h _ => by rw [smul_smul]
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hh
    exact ⟨hHc v, hfree v hv⟩

end MMP.Fourfold
