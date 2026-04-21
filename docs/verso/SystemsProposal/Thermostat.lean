import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems
open Systems.Examples

set_option pp.rawOnError true

#doc (Manual) "The Thermostat — Your Example, Three Frameworks" =>

You used the thermostat in the 1995 paper to derive the internal-state requirement (Proposition 29) and the semantic-relation argument. Here it is formalized under all three frameworks. 160 lines of Lean, zero `sorry`s.

# Entities and Action

Five entities. Four causal bonds.

```lean
#check Entity
#check entityActsOn
```

A modeling decision: outsideAir does not act on anything discretely — its thermal effect enters through the milieu $`M`, not a point-source flow. This is the engineering judgment Mobus's $`E = \langle O, M \rangle` decomposition makes possible and Bunge's flat $`E` does not.

# Building the Mobus System

The historical direction is Klir → Bunge → Mobus: increasing elaboration over 43 years. The formal direction is the reverse: Mobus → Bunge → Klir, increasing abstraction through projection. We follow the formal direction because it reveals the convergence — and because it preserves what the history obscures. Building *up* from Klir would suggest Mobus extends Bunge, which is exactly the "systematic extension" framing your question killed. Mobus never read Bunge. Building *down* from Mobus lets each framework stand independently, and the projections show where they meet without implying one derives from the other. The information loss table below shows exactly what each step of abstraction discards.

We build the Mobus system first — it carries the most information — then derive the others by projection.

```lean
#check thermostatMobus
```

The parametric fields are telling: transforms = `Unit`, history = `Unit`, timeScale = `Unit`. We have a structural skeleton but no theory of what the controller *does*, what it *remembers*, or *how fast* it operates.

# Bunge and Klir — By Projection

Rather than defining independently, we *extract* them from the Mobus 8-tuple via the projection maps:

```lean
#check thermostatBunge
#check thermostatKlir
```

A structural observation: **room appears in the relation but not in the thing-set.** After the Bunge → Klir projection, the pairs (room, thermometer) and (furnace, room) are in $`R`, but room $`\notin T`. Room becomes a *phantom entity* — present in the system's relational structure but not counted among its things. This is the formal content of losing the environment component $`E`.

# The Triangle on This Instance

```lean
#check thermostat_triangle_commutes
```

`rfl`. Both paths from the Mobus thermostat to the Klir system produce definitionally identical values.

**What was lost at each step:**

| Lost | Thermostat Content | Why It Matters |
|---|---|---|
| Milieu $`M` | Ambient temperature, humidity | The disturbance source control₂ requires |
| Capacity $`\kappa` | BTUs, millivolts, on/off | Magnitude of flows — invisible to Bunge |
| Boundary $`\pi` | Thermal insulation R-value | How much disturbance penetrates |
| Transforms $`\tau` | The if/then control rule | The semantic relation, the rule, the sign |
| History $`\eta` | Recent temperature readings | Memory — PID needs integral term |
| Time scale $`\delta` | 30-second polling interval | Can the system track fast disturbances? |

**Mobus → Bunge.** Milieu $`M` disappears (ambient temperature and humidity vanish). Capacity labels disappear (the distinction between a temperature signal, a binary command, and a heat-energy flow is collapsed — all become bare pairs). Boundary properties, transforms, history, and time scale disappear.

**Bunge → Klir.** Environment $`E` disappears. The distinction between "inside" and "outside" is lost. Room becomes a phantom in $`R`; outsideAir disappears entirely (it has no bonds).

**But all three descriptions miss the same thing.** The controller's logic — *if temperature < setpoint then turn on furnace* — is a *rule*, not a law. It was selected from a variety of possible control functions. It could have been a PID controller, a bang-bang controller, or a machine-learning policy. Two Mobus thermostats differing only in transforms — one with bang-bang control, one with PID — project to the **same** Bunge CES triple. They are structurally identical. They differ only in what the controller *does*.

This is precisely your point from the 1995 paper: the feedback function $`f : O_i \to O_e` *must be a rule (contingent entailment), not a natural law*. Rules are arbitrary, conventional, and selected — exactly the properties of Peircean signs. The formalization reaches its limit here.
