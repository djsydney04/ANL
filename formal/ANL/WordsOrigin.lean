import ANL.WordsMachine
import ANL.WordsTyping
import ANL.MemoryOrigin

namespace ANL.Words

open ANL.Memory

def SiteAllowed (p : Program) (site : Site) : Prop :=
  ∃ fn, p.functions[site.function]? = some fn ∧ site.heap ∈ fn.body.heapSites

def TermAllowed (p : Program) (function : Nat) (term : Term) : Prop :=
  ∀ site ∈ term.heapSites, SiteAllowed p ⟨function, site⟩

def TermsAllowed (p : Program) (function : Nat) (terms : List Term) : Prop :=
  ∀ term ∈ terms, TermAllowed p function term

def Frame.Allowed (p : Program) (f : Nat) : Frame → Prop
  | .bind _ b => TermAllowed p f b
  | .ifF yes no => TermAllowed p f yes ∧ TermAllowed p f no
  | .left _ rhs => TermAllowed p f rhs
  | .arguments _ _ remaining _ | .fields remaining _ => TermsAllowed p f remaining
  | .condition c b | .body c b => TermAllowed p f c ∧ TermAllowed p f b
  | .heapLength site init yes no => site.function = f ∧ SiteAllowed p site ∧
      TermAllowed p f init ∧ TermAllowed p f yes ∧ TermAllowed p f no
  | .heapInitial site _ yes no => site.function = f ∧ SiteAllowed p site ∧
      TermAllowed p f yes ∧ TermAllowed p f no
  | .owner _ site => site.function = f ∧ SiteAllowed p site
  | .writeIndex _ value => TermAllowed p f value
  | _ => True

def KontOrigin (p : Program) : Nat → List Frame → Prop
  | _, [] => True
  | _, .callReturn caller _ :: k => KontOrigin p caller.function k
  | f, frame :: k => frame.Allowed p f ∧ KontOrigin p f k

def Control.Allowed (p : Program) (f : Nat) : Control → Prop
  | .eval term => TermAllowed p f term
  | .lengthReady site _ init yes no => site.function = f ∧ SiteAllowed p site ∧
      TermAllowed p f init ∧ TermAllowed p f yes ∧ TermAllowed p f no
  | .allocate site _ _ yes no => site.function = f ∧ SiteAllowed p site ∧
      TermAllowed p f yes ∧ TermAllowed p f no
  | .writeCheck _ _ value => TermAllowed p f value
  | .close _ site _ => site.function = f ∧ SiteAllowed p site
  | _ => True

def State.Origin (p : Program) (s : State) : Prop :=
  s.control.Allowed p s.current.function ∧ KontOrigin p s.current.function s.kont

theorem function_body_allowed (h : p.functions[f]? = some fn) : TermAllowed p f fn.body := by
  intro site member
  exact ⟨fn, h, member⟩

theorem beginArguments_origin (ha : TermsAllowed p a.function args) (hk : KontOrigin p a.function k) :
    State.Origin p (beginArguments f loan args values a k w) := by
  cases args with
  | nil => exact ⟨trivial, hk⟩
  | cons e rest =>
    exact ⟨ha e List.mem_cons_self, (fun x hx => ha x (List.mem_cons_of_mem e hx)), hk⟩

theorem resume_origin (hk : KontOrigin p a.function k) : State.Origin p (resume result a k w) := by
  cases result <;> exact ⟨trivial, hk⟩

set_option linter.unusedSimpArgs false in
theorem origin_preservation (h : State.Origin p s) (hs : Step p responses s next) : State.Origin p next := by
  cases hs <;> try exact h
  all_goals try (exact resume_origin h.2.2)
  all_goals try (exact resume_origin h.2)
  all_goals try (apply beginArguments_origin)
  all_goals try (simp_all [State.Origin, Control.Allowed, KontOrigin, Frame.Allowed, TermsAllowed,
    TermAllowed, Term.heapSites, List.mem_append, List.mem_flatMap, or_imp, forall_and])
  case call.ha => intro e he site hs; exact h.1 site e he hs
  case tupleFirst => intro e he site hs; exact h.1.2 site e he hs
  case callView.ha => intro e he site hs; exact h.1 site e he hs
  case argumentReturn.ha => exact h.1
  case fieldNext => exact h.1.2
  case grant hf => exact function_body_allowed hf

theorem initial_origin (p : Program) : State.Origin p (initial p) := ⟨trivial, trivial⟩

theorem steps_origin (h : State.Origin p s) (hs : Steps p responses s last) : State.Origin p last := by
  induction hs with | refl => exact h | head hs _ ih => exact ih (origin_preservation h hs)

theorem entry_origin (hs : Steps p responses (initial p) last) : State.Origin p last :=
  steps_origin (initial_origin p) hs

theorem SiteAllowed.canonical (wf : WellFormedProgram p) (h : SiteAllowed p site) :
    ∃ fn, p.functions[site.function]? = some fn ∧ fn.id = site.function ∧
      site.heap < fn.body.heapSites.length := by
  obtain ⟨fn, hf, hm⟩ := h
  have canonical := (wf.function_at hf).sites
  change fn.body.heapSites = List.range fn.body.heapSites.length at canonical
  rw [canonical, List.mem_range] at hm
  exact ⟨fn, hf, wf.function_id hf, hm⟩

def TraceOrigin (p : Program) (w : World) : Prop :=
  ∀ event ∈ w.trace, SiteAllowed p event.site

theorem trace_origin_congr {w next : World} (h : TraceOrigin p w) (he : next.trace = w.trace) : TraceOrigin p next := by
  simpa only [TraceOrigin, he] using h

theorem trace_append_allowed {events : List Event} {event : Event} (h : ∀ event ∈ events, SiteAllowed p event.site)
    (ha : SiteAllowed p event.site) : ∀ e ∈ events ++ [event], SiteAllowed p e.site := by
  intro e he
  rcases List.mem_append.mp he with before | last
  · exact h e before
  · have eq := List.mem_singleton.mp last
    simpa only [eq] using ha

theorem allocate_trace_origin {w : World} (h : TraceOrigin p w) (siteAllowed : SiteAllowed p site) :
    TraceOrigin p (allocate p.profile responses w site n init).2 := by
  by_cases hb : p.profile.maxCells < n
  · rw [allocate_target hb]; exact h
  · by_cases hz : n = 0
    · subst n
      unfold TraceOrigin
      rw [allocate_empty_trace.2.2]
      exact trace_append_allowed h siteAllowed
    · have hn : 0 < n := by omega
      have bound : n ≤ p.profile.maxCells := by omega
      unfold TraceOrigin
      rw [(allocate_request_trace hn bound).2.2]
      exact trace_append_allowed h siteAllowed

theorem allocate_eq_trace_origin {w next : World} (h : TraceOrigin p w) (siteAllowed : SiteAllowed p site)
    (ha : allocate p.profile responses w site n init = (result, next)) : TraceOrigin p next := by
  have origin := allocate_trace_origin (responses := responses) (n := n) (init := init) h siteAllowed
  simpa only [ha] using origin

theorem close_trace_origin {w next : World} (h : TraceOrigin p w) (siteAllowed : SiteAllowed p site)
    (hc : w.close ref site = some next) : TraceOrigin p next := by
  unfold TraceOrigin
  rw [World.close_trace hc]
  apply trace_append_allowed h
  cases ref <;> exact siteAllowed

theorem resume_trace_origin (h : TraceOrigin p w) : TraceOrigin p (resume result a k w).world := by
  cases result <;> exact h

theorem step_trace_origin (ho : State.Origin p s) (h : TraceOrigin p s.world)
    (hs : Step p responses s next) : TraceOrigin p next.world := by
  cases hs <;> try exact h
  all_goals try exact resume_trace_origin h
  case call => cases ‹List Term› <;> exact h
  case callView => cases ‹List Term› <;> exact h
  case argumentReturn => cases ‹List Term› <;> exact h
  case allocated ha => exact allocate_eq_trace_origin h ho.1.2.1 ha
  case allocationRefused ha => exact allocate_eq_trace_origin h ho.1.2.1 ha
  case allocationRejected ha => exact allocate_eq_trace_origin h ho.1.2.1 ha
  case stored hs => exact trace_origin_congr h (World.write_footprint hs).2.2.2
  case closed hc => exact close_trace_origin h ho.1.2 hc

theorem steps_trace_origin (ho : State.Origin p s) (h : TraceOrigin p s.world)
    (hs : Steps p responses s last) : TraceOrigin p last.world := by
  induction hs with
  | refl => exact h
  | head hs _ ih => exact ih (origin_preservation ho hs) (step_trace_origin ho h hs)

theorem entry_trace_origin (hs : Steps p responses (initial p) last) : TraceOrigin p last.world :=
  steps_trace_origin (initial_origin p) (by simp [initial, TraceOrigin, World.initial, World.trace]) hs

theorem entry_event_site (wf : WellFormedProgram p) (hs : Steps p responses (initial p) last)
    (eventMember : event ∈ last.world.trace) :
    ∃ fn, p.functions[event.site.function]? = some fn ∧ fn.id = event.site.function ∧
      event.site.heap < fn.body.heapSites.length :=
  (entry_trace_origin hs event eventMember).canonical wf

end ANL.Words
