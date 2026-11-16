module
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem

/-!
# Generic local data along the singular curves of an exceptional model

Let `r : Z ⟶ Y` be a curve-and-point exceptional model
(`MMP.Fourfold.IsCurvePointExceptionalModel`) with snc exceptional divisor `F = ∑ Fᵢ`, and let
`T ⊆ Sing Y` be a singular curve, so that `(Y, 0, T, r)` is a local setting. The exceptional snc
strata are the closed subschemes `F_J = ⋂_{i ∈ J} Fᵢ` for the nonempty sets `J` of components of
`F`. A Zariski-open `T° ⊆ T` is *stratum-smooth adapted* if it is an `r`-adapted open
(`MMP.Fourfold.IsAdaptedOpen`: connected, dense, smooth, with `(R²j_* ℚ)|_{T°}` and
`(R²r_* ℚ)|_{T°}` local systems and `r` flat and projective over it) such that
every stratum `F_J ×_Y T° ⟶ T°` is smooth.

On such a `T°` the resolution local system `W_T = (R²r_* ℚ_Z)|_{T°}`, with fibre `H²(F_t, ℚ)`, is
`MMP.Fourfold.resolutionLocalSystem`, the punctured local system `V_T` is
`MMP.Fourfold.curveLocalSystem`, and the restriction map `r : W_T ⟶ V_T` is
`MMP.Fourfold.localSystemRestriction`.

## Main definitions

* `MMP.Fourfold.IsStratumSmoothAdaptedOpen`: `r`-adapted opens of `T` over which the exceptional
  snc strata are smooth.

## Main results

* `MMP.Fourfold.IsStratumSmoothAdaptedOpen.of_le`: any connected dense Zariski-open subset of a
  stratum-smooth adapted open is again one.

## Implementation notes

The stratum `F_J` is the closed subscheme cut out by the ideal sheaf `∑_{i ∈ J} 𝓘_{Fᵢ}`, the
scheme-theoretic intersection of the `Fᵢ`; smoothness over `T°` is smoothness of its base change
`F_J ×_Y T° ⟶ T°`. The local systems `W_T`, `V_T` and the map `r` are those of the punctured local
system of `T`, which are defined for every Zariski-open of `T`.

Shrinking `T°` to a connected dense open `T°' ⊆ T°` preserves each clause: the punctured and
resolution sheaves on `T°'` are the inverse images of those on `T°` along the realization of
`T°' ⟶ T°`, and inverse images of local systems are local systems; smoothness of `T°'`, flatness
and projectivity of `Z ×_Y T°' ⟶ T°'`, and smoothness of the strata over `T°'` follow by
composition with, or base change along, the open immersion `T°' ⟶ T°`.
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

variable {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y} (r : Z ⟶ Y)

/-- A *stratum-smooth `r`-adapted open* of the curve `T`: an `r`-adapted open `T° ⊆ T`
(in particular connected and dense) such that for every nonempty set `J` of components of the
divisor `F`, the stratum `F_J = ⋂_{i ∈ J} Fᵢ` is smooth over `T°`, i.e. `F_J ×_Y T° ⟶ T°` is
smooth. -/
@[mmp "def_mmp_conductor_curve_local_data"]
public structure IsStratumSmoothAdaptedOpen (F : Divisor Z) (To : (curveScheme T).Opens) : Prop
    extends IsAdaptedOpen sY r To where
  /-- Every exceptional snc stratum `F_J`, `∅ ≠ J ⊆ supp F`, is smooth over `T°`. -/
  smooth_stratum : ∀ J ⊆ F.support, J.Nonempty →
    Smooth (pullback.snd ((J.sup PrimeDivisor.idealSheaf).subschemeι ≫ r) (To.ι ≫ curveι T))

/-! ### Shrinking a stratum-smooth adapted open -/

section Shrinking

open MMP.Analytic MMP.Analytic.ComplexPoints Opposite

/-- Inverse images of sheaves on topological spaces compose. -/
private noncomputable def sheafPullbackCompIso {X₁ X₂ X₃ : TopCat.{0}} (g : X₁ ⟶ X₂)
    (f : X₂ ⟶ X₃) :
    TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (g ≫ f) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g)).ofNatIsoRight
      (NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl)).leftAdjointUniq
        (TopCat.Sheaf.pullbackPushforwardAdjunction _ (g ≫ f))

/-- The inverse image of a constant sheaf is constant. -/
private noncomputable def sheafPullbackConstIso {X₁ X₂ : TopCat.{0}} (f : X₁ ⟶ X₂) :
    constantSheaf (Opens.grothendieckTopology X₂) (ModuleCat.{0} ℚ) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ≅
      constantSheaf (Opens.grothendieckTopology X₁) (ModuleCat.{0} ℚ) :=
  (((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)).ofNatIsoRight
      (NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl)).leftAdjointUniq
        (constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop)

/-- Being a local system is invariant under isomorphism. -/
private theorem isLocalSystem_of_iso {X₁ : TopCat.{0}} {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X₁}
    (e : F ≅ G) (hF : IsLocalSystem F) : IsLocalSystem G := by
  intro x
  obtain ⟨V, hxV, E, hE, ⟨e'⟩⟩ := hF x
  exact ⟨V, hxV, E, hE,
    ⟨(TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) V.inclusion').mapIso e.symm ≪≫ e'⟩⟩

/-- The inverse image of a local system along a continuous map is a local system. -/
private theorem isLocalSystem_pullback {X₁ X₂ : TopCat.{0}} (f : X₁ ⟶ X₂)
    {F : TopCat.Sheaf (ModuleCat.{0} ℚ) X₂} (hF : IsLocalSystem F) :
    IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F) := by
  intro x
  obtain ⟨V, hxV, E, hE, ⟨e⟩⟩ := hF (f x)
  let U : Opens X₁ := (Opens.map f).obj V
  let g : (Opens.toTopCat X₁).obj U ⟶ (Opens.toTopCat X₂).obj V :=
    TopCat.ofHom ⟨fun y => ⟨f y.1, y.2⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hg : U.inclusion' ≫ f = g ≫ V.inclusion' := rfl
  exact ⟨U, hxV, E, hE, ⟨(sheafPullbackCompIso U.inclusion' f).app F ≪≫
    eqToIso (congrArg (fun φ => (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) φ).obj F) hg) ≪≫
    (sheafPullbackCompIso g V.inclusion').symm.app F ≪≫
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).mapIso e ≪≫ (sheafPullbackConstIso g).app E⟩⟩

/-- A property stable under base change passes from `X ×_S S' ⟶ S'` to `X ×_S T' ⟶ T'` for
`T' ⟶ S' ⟶ S`. -/
private theorem pullback_snd_of_comp {P : MorphismProperty Scheme.{0}}
    [P.IsStableUnderBaseChange] {X S S' T' : Scheme.{0}} (f : X ⟶ S) {h : S' ⟶ S}
    {g' : T' ⟶ S'} {k : T' ⟶ S} (hk : g' ≫ h = k) (hf : P (pullback.snd f h)) :
    P (pullback.snd f k) := by
  subst hk
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f h g']
  exact (P.cancel_left_of_respectsIso _ _).mpr (P.pullback_snd _ _ hf)

/-- H-projectivity passes from `X ×_S S' ⟶ S'` to `X ×_S T' ⟶ T'` for `T' ⟶ S' ⟶ S`. -/
private theorem isProjectiveMorphism_pullback_snd_of_comp {X S S' T' : Scheme.{0}} (f : X ⟶ S)
    {h : S' ⟶ S} {g' : T' ⟶ S'} {k : T' ⟶ S} (hk : g' ≫ h = k)
    (hf : IsProjectiveMorphism (pullback.snd f h)) : IsProjectiveMorphism (pullback.snd f k) := by
  subst hk
  obtain ⟨n, i, hi, hi'⟩ := hf.baseChange g'
  exact ⟨n, (pullbackLeftPullbackSndIso f h g').inv ≫ i, inferInstance, by
    rw [Category.assoc, hi', pullbackLeftPullbackSndIso_inv_snd_snd]⟩

variable {sY r} {F : Divisor Z}

/-- **Shrinking a stratum-smooth adapted open.** A connected dense Zariski-open `T°' ⊆ T°` of a
stratum-smooth `r`-adapted open `T°` is again a stratum-smooth `r`-adapted open. -/
@[mmp "def_mmp_conductor_curve_local_data"]
public theorem IsStratumSmoothAdaptedOpen.of_le {To To' : (curveScheme T).Opens}
    (h : IsStratumSmoothAdaptedOpen sY r F To) (hle : To' ≤ To) (hconn : ConnectedSpace To')
    (hdense : Dense (To' : Set (curveScheme T))) : IsStratumSmoothAdaptedOpen sY r F To' := by
  let ι : (To' : Scheme.{0}) ⟶ To := (curveScheme T).homOfLE hle
  have hι : ι ≫ To.ι ≫ curveι T = To'.ι ≫ curveι T := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have hιs : ι ≫ To.ι ≫ curveι T ≫ sY = To'.ι ≫ curveι T ≫ sY := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  let a := analyticMap ι hιs
  have ha : a ≫ curveOpenInclusion sY To = curveOpenInclusion sY To' := by
    ext x
    change (x.hom ≫ ι) ≫ To.ι ≫ curveι T = x.hom ≫ To'.ι ≫ curveι T
    rw [Category.assoc, hι]
  have hloc : ∀ G : TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sY),
      IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY To)).obj G) →
      IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY To')).obj G) :=
    fun G hG => isLocalSystem_of_iso ((sheafPullbackCompIso a (curveOpenInclusion sY To)).app G ≪≫
      eqToIso (congrArg (fun φ => (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) φ).obj G) ha))
      (isLocalSystem_pullback a hG)
  have hsm : Smooth (To'.ι ≫ curveι T ≫ sY) := by
    rw [← hιs]
    have := h.smooth
    infer_instance
  exact
    { connectedSpace := hconn
      smooth := hsm
      dense := hdense
      isLocalSystem := hloc _ h.isLocalSystem
      isLocalSystem_resolution := hloc _ h.isLocalSystem_resolution
      topologicalKrullDim_fibre_le := fun t => h.topologicalKrullDim_fibre_le ⟨t.1, hle t.2⟩
      flat := pullback_snd_of_comp (P := @Flat) r hι h.flat
      isProjectiveMorphism := isProjectiveMorphism_pullback_snd_of_comp r hι h.isProjectiveMorphism
      smooth_stratum := fun J hJ hne =>
        pullback_snd_of_comp (P := @Smooth) _ hι (h.smooth_stratum J hJ hne) }

end Shrinking

end MMP.Fourfold
