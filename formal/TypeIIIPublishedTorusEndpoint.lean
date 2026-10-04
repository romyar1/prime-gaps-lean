import TypeIIIPublishedTypeIII
import TypeIIITorusStalkCriterion

/-!
# The published application route without baseline norm hypotheses

Every existing Application uses the literal unit torus as physical open.
The exact zero-extension argument removes BaselineLocalInputs from both
exceptional branches and the uniform endpoint. All geometric, arithmetic,
weight and support assumptions in Application remain unchanged.
-/

noncomputable section

namespace PrimeGap182.TypeIII.PublishedTypeIII

open PublishedStalkCertificate

universe u v

namespace Application

variable {B Rphys Dcore Nproper Npunct p : ℕ} [Fact p.Prime]
  {α m m' n n' : ZMod p} {theory : Theory.{u,v} p}
  (app : Application B Rphys Dcore Nproper Npunct p α m m' n n' theory)

theorem certificate_physicalOpen : app.certificate.physicalOpen = torusOpen p := rfl

include app in
theorem finiteFourierBound_on_torus (hp : cutoff Nproper Npunct < p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hdistinct : m ≠ m' ∧ n ≠ n') :
    FiniteExceptionalFourierBound p (uniformStalkConstant B 1 Rphys)
      (15 * Dcore) α m m' n n' :=
  TorusStalkCriterion.finiteFourierBound
    (app.finiteSupport hp hα hm hm' hn hn' hdistinct)
    (by rw [app.certificate_physicalOpen])

include app in
theorem curveFourierBound_on_torus (hp : cutoff Nproper Npunct < p) :
    CurveExceptionalFourierBound p (uniformStalkConstant B 1 Rphys)
      (15 * Dcore) α m m' n n' :=
  TorusStalkCriterion.curveFourierBound (app.curveSupport hp)
    (by rw [app.certificate_physicalOpen])

end Application

namespace UniformApplications

variable {B Rphys Dcore Nproper Npunct : ℕ}
  (apps : UniformApplications.{u,v} B Rphys Dcore Nproper Npunct)

include apps in
/-- Exact original local proposition, with no baseline estimate premise. -/
theorem localFourierHypothesis_on_torus :
    LocalFourierHypothesis (uniformStalkConstant B 1 Rphys) (15 * Dcore)
      (cutoff Nproper Npunct) := by
  intro p _ hp α m m' n n' hα hm hm' hn hn'
  let app := apps.application p hp α m m' n n' hα hm hm' hn hn'
  exact ⟨fun hd => app.finiteFourierBound_on_torus hp hα hm hm' hn hn' hd,
    fun _ => app.curveFourierBound_on_torus hp⟩

include apps in
theorem hasFiniteExceptionalTypeIIIInput_on_torus : HasFiniteExceptionalTypeIIIInput :=
  ⟨uniformStalkConstant B 1 Rphys, uniformStalkConstant_pos B 1 Rphys,
    15 * Dcore, cutoff Nproper Npunct, apps.localFourierHypothesis_on_torus⟩

end UniformApplications

end PrimeGap182.TypeIII.PublishedTypeIII

#print axioms PrimeGap182.TypeIII.PublishedTypeIII.Application.certificate_physicalOpen
#print axioms PrimeGap182.TypeIII.PublishedTypeIII.Application.finiteFourierBound_on_torus
#print axioms PrimeGap182.TypeIII.PublishedTypeIII.Application.curveFourierBound_on_torus
#print axioms PrimeGap182.TypeIII.PublishedTypeIII.UniformApplications.localFourierHypothesis_on_torus
#print axioms PrimeGap182.TypeIII.PublishedTypeIII.UniformApplications.hasFiniteExceptionalTypeIIIInput_on_torus
