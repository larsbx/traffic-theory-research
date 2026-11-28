import FieldEvidenceCheck
import TrafficEventsCheck
import TrafficWorkCheck

/-- The event kernel, work accounting and field observations deliberately use
different packet types. A field sample cannot be passed as a model event. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--field", path] => FieldEvidenceCheck.run path
  | ["--events", path] => TrafficEventsCheck.run path
  | ["--work", path] => TrafficWorkCheck.run path
  | _ =>
    IO.eprintln "usage: traffic_evidence_check (--field|--events|--work) CASES.json"
    return 2
