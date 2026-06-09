/-
  Systems/Core/Improvability.lean
  Principle 12: Improvability — "Systems can be improved." (Engineering.)

  Mobus labels #12 a COROLLARY of Evolution (#6). This file argues, formally, that the
  corollary framing is misplaced: improvement is not blind evolution but its opposite —
  *directed* change by an external agent — and #12 belongs with #11 in an agential layer
  the ontological principles (#1–#10) do not contain.

  EVOLUTION IS BLIND; ENGINEERING IS DIRECTED.
  Evolution (#6) has no goal: variation is random, selection is environmental. Engineering
  has a goal and a designer who holds a model of the system (#9), *understands* it (#11),
  and *intervenes from outside its boundary* to move it toward that goal. Calling
  Improvability a corollary of Evolution is like calling architecture a corollary of
  erosion — both reshape structures, but only one has intention.

  THE FORMALIZATION (the agency framing). Two layers:

  - `Improvement S` — the bare directed move: native dynamics `dyn`, a `goal` (an external
    set-point), and an `intervene : (S → S) → (S → S)` that rewrites the law *from outside*
    so the goal becomes a rest state (`improves`), where it was not one before (`genuine`).
    `intervene` is a map ON dynamics, not an internal action — this is the "intervention
    from outside the boundary" that #4 (fixed law) and #6 (internal/environmental change)
    lack.

  - `DirectedAgent S M` — the full agent: it carries an `Understanding S M` (#11) of the
    system it acts on, plus the goal and intervention. So **#12 ⟹ #11 by construction**
    (`toUnderstanding`): you cannot deliberately improve what you do not understand.

  WHAT IS PROVED.
  - `Improvement.persists`: the directed outcome is stable at every horizon — once the
    intervention makes the goal an equilibrium, the improved system stays there forever
    (`equilibrium_iterate`). The #12 analogue of #11's all-horizon `tracks`.
  - `DirectedAgent.toUnderstanding` / `toImprovement`: #12 presupposes #11, and forgets to
    its own bare core.
  - `Homeostat.toImprovement`: a governance homeostat (#8) IS an improvement engine — its
    set-point is the goal, its feedback law is the intervention, and `target_is_equilibrium`
    supplies `improves`. Governance is the realized special case of directed improvement.
  - `goal_is_external`: the SAME dynamics admit improvements toward DIFFERENT goals, so the
    goal is not a function of the system — it is genuinely added structure (the roadmap's
    "a goal not supplied by the system's own dynamics"). This is the independence content.
  - `cyclic3_no_directed_improvement`: the **3-cycle on `Fin 3`** — a system that has a
    model yet cannot be understood (today's `cyclic3_no_understanding`) — admits NO directed
    agent. A prime-cyclic system can be blindly evolved (#6) but not deliberately improved
    (#12): the un-understandable is un-engineerable. This is exactly where #12 parts from #6.
  - `noisyPairDirectedAgent`: a concrete agent (reusing today's `noisyPairUnderstanding`),
    so the structure is non-vacuous.

  THE FINDING — the agential layer (the roadmap's "most interesting" question, answered).
  #11 and #12 are the two channels of the designer's lens onto a system:
    Understanding (#11) = GET / observe  — read state out  (`abstract : S → M`)
    Improvement   (#12) = PUT / intervene — write structure in (`intervene` on the dynamics)
  Together with the model (#9) they form the agent's bidirectional grip — the homeostat
  already carries both (`Homeostat.toLens` get/put, `Homeostat.toImprovement` the directed
  put). So the 12 principles split: **10 ontological** (what systems ARE and DO) + **2
  agential** (#11 observe, #12 intervene — what an agent does WITH a system). And the two
  agential principles *interact*: directed improvement requires understanding, so the
  un-understandable is un-engineerable. That interaction is the formal seam between #12 and
  blind #6. Mobus's "corollary of #6" is misplaced exactly as #11's "corollary of #9" was.

  Deferred (research-level, not gaps): objective-increase / fitness-landscape framing (needs
  an order on S); Ashby's requisite variety as a bound on improvability; the agent predicting
  its own improvement (`Understanding.tracks` on the *intervened* law); global convergence from
  arbitrary starts (needs a metric/attractor); and the weaker #9-only dependency (improvement
  via a faithful model rather than full compression).
-/

import Systems.Core.Understanding
import Systems.Core.Governance

namespace Systems

/-! ## Improvement — directed intervention toward an external goal -/

/-- An `Improvement` of a system with native dynamics `dyn : S → S`: an external `goal`
    and an `intervene : (S → S) → (S → S)` that rewrites the law so the goal becomes a rest
    state (`improves`) where it was not one natively (`genuine`).

    `intervene` acts ON the dynamics from outside — the intentional intervention from outside
    the boundary that distinguishes engineering from a fixed law (#4) or blind change (#6). -/
structure Improvement (S : Type*) where
  /-- The system's native (uncontrolled) dynamics. -/
  dyn : S → S
  /-- The agent's target — an external set-point, not supplied by `dyn`. -/
  goal : S
  /-- The intervention: a transformation of the dynamics applied from outside the boundary. -/
  intervene : (S → S) → (S → S)
  /-- The intervention makes the goal an equilibrium of the resulting dynamics. -/
  improves : IsEquilibrium (intervene dyn) goal
  /-- Genuine improvement: the goal was not already a rest state of the native dynamics. -/
  genuine : ¬ IsEquilibrium dyn goal

/-- The directed outcome is stable at every horizon: once the intervention makes the goal an
    equilibrium, the improved system started at the goal stays there forever. The #12
    counterpart of #11's all-horizon `tracks`. -/
theorem Improvement.persists {S : Type*} (imp : Improvement S) (n : ℕ) :
    (imp.intervene imp.dyn)^[n] imp.goal = imp.goal :=
  equilibrium_iterate imp.improves n

/-! ## DirectedAgent — the full agency framing (#12 presupposes #11)

  An agent that understands the system (#11) and intervenes on it toward a goal. The
  `understanding` field makes the dependency #12 ⟹ #11 structural. -/

/-- A `DirectedAgent` improving a system: it carries an `Understanding S M` of the system
    (the observe/GET channel, #11), a `goal`, and an `intervene` (the PUT channel) that makes
    the goal a rest state of the understood system's dynamics, where it was not one before. -/
structure DirectedAgent (S M : Type*) where
  /-- The agent's understanding of the system it acts on (#11 — the GET/observe channel). -/
  understanding : Understanding S M
  /-- The agent's target. -/
  goal : S
  /-- The intervention on the system's dynamics (the PUT/intervene channel). -/
  intervene : (S → S) → (S → S)
  /-- The intervention makes the goal an equilibrium of the understood system's dynamics. -/
  improves : IsEquilibrium (intervene understanding.systemDyn) goal
  /-- Genuine improvement: the goal was not already a native rest state. -/
  genuine : ¬ IsEquilibrium understanding.systemDyn goal

/-- **#12 ⟹ #11.** A directed agent presupposes an understanding of the system it improves:
    you cannot deliberately improve what you do not understand. The headline dependency, by
    projection. -/
def DirectedAgent.toUnderstanding {S M : Type*} (a : DirectedAgent S M) : Understanding S M :=
  a.understanding

/-- A directed agent forgets to its bare directed move on the understood system. -/
def DirectedAgent.toImprovement {S M : Type*} (a : DirectedAgent S M) : Improvement S where
  dyn := a.understanding.systemDyn
  goal := a.goal
  intervene := a.intervene
  improves := a.improves
  genuine := a.genuine

/-! ## Governance (#8) is the realized improvement engine -/

/-- A homeostat is an improvement engine: its set-point is the goal, its feedback law is the
    intervention, and `Homeostat.target_is_equilibrium` (#8) supplies `improves`. The
    corrective `put` channel of governance, directed by the reference value, IS the #12
    intervention. Requires the native `dyn` not already rest at the target (`h_genuine`). -/
def Homeostat.toImprovement {S O : Type*} (h : Homeostat S O) (s : S) (dyn : S → S)
    (h_at : h.atTarget s)
    (h_error_zero : ∀ o, h.error o o = h.error h.setPoint h.setPoint)
    (h_correct_neutral : ∀ s', h.correct (h.error h.setPoint h.setPoint) s' = s')
    (h_genuine : ¬ IsEquilibrium dyn s) : Improvement S where
  dyn := dyn
  goal := s
  intervene := fun _ => h.feedbackLaw
  improves := h.target_is_equilibrium s h_at h_error_zero h_correct_neutral
  genuine := h_genuine

/-! ## The goal is external structure — the independence content

  The same dynamics admit improvements toward different goals, so the goal is not determined
  by the system. Improvement adds structure (goal + intervention) no system-internal
  principle supplies. -/

/-- A directed improvement of `Bool` under the toggle dynamics `not` (which has no native
    equilibrium) toward an arbitrary goal `g`, by the intervention "drive straight to `g`". -/
def boolImprovement (g : Bool) : Improvement Bool where
  dyn := not
  goal := g
  intervene := fun _ => Function.const Bool g
  improves := rfl
  genuine := by cases g <;> simp [IsEquilibrium]

/-- **The goal is not a function of the dynamics.** One system (`Bool` under `not`), two
    improvements toward two different goals. The goal — and the intervention realizing it —
    is added structure, exactly the roadmap's "a goal not supplied by the system's own
    dynamics." This is what makes #12 independent of the ontological principles. -/
theorem goal_is_external :
    ∃ (dyn : Bool → Bool) (imp₁ imp₂ : Improvement Bool),
      imp₁.dyn = dyn ∧ imp₂.dyn = dyn ∧ imp₁.goal ≠ imp₂.goal :=
  ⟨not, boolImprovement true, boolImprovement false, rfl, rfl, by decide⟩

/-! ## The un-understandable is un-engineerable — where #12 parts from #6 -/

/-- **#12 ⇏ #6.** The 3-cycle on three states has a model (every system does) yet cannot be
    understood (`cyclic3_no_understanding`, today) — so it admits NO directed agent: a
    `DirectedAgent` carries an `Understanding`, and there is none for prime-cyclic dynamics.
    A prime-cyclic system can be blindly evolved (#6) but not deliberately improved (#12).
    Directed engineering requires understanding; the un-understandable marks its hard limit. -/
theorem cyclic3_no_directed_improvement {M : Type*} (a : DirectedAgent (Fin 3) M)
    (h : ∀ x : Fin 3, a.understanding.systemDyn x = x + 1) : False :=
  cyclic3_no_understanding a.understanding h

/-! ## Non-vacuity -/

/-- A concrete directed agent, reusing today's `noisyPairUnderstanding`: the agent understands
    the system (keeps the conserved coordinate, discards the noisy one) and intervenes to fix
    the conserved state at `(true, true)`. The native dynamics toggle the noisy coordinate and
    so have no equilibrium, making the improvement genuine. -/
def noisyPairDirectedAgent : DirectedAgent (Bool × Bool) Bool where
  understanding := noisyPairUnderstanding
  goal := (true, true)
  intervene := fun _ => Function.const (Bool × Bool) (true, true)
  improves := rfl
  genuine := by simp [IsEquilibrium, noisyPairUnderstanding]

end Systems
