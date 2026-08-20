# Three ob3ects, ready to run

Each ask is one or two lines and names no candidate, so the pipeline imscribes the
object rather than grading a guess. The context folder grounds all three.

```
cd ~/imsgct

python3 ob3ect/auto.py --desc-file p4rakernel/p4ramill/Imscribing/Millennium/Erdos/collatz_context/ask_mixing.txt \
  --name collatz_level_contraction \
  --context p4rakernel/p4ramill/Imscribing/Millennium/Erdos/collatz_context \
  --provider openrouter --model google/gemini-3-flash-preview --retries inf

python3 ob3ect/auto.py --desc-file p4rakernel/p4ramill/Imscribing/Millennium/Erdos/collatz_context/ask_open_arm.txt \
  --name collatz_open_arm \
  --context p4rakernel/p4ramill/Imscribing/Millennium/Erdos/collatz_context \
  --provider openrouter --model google/gemini-3-flash-preview --retries inf

python3 ob3ect/auto.py --desc-file p4rakernel/p4ramill/Imscribing/Millennium/Erdos/collatz_context/ask_two_readings.txt \
  --name collatz_two_readings \
  --context p4rakernel/p4ramill/Imscribing/Millennium/Erdos/collatz_context \
  --provider openrouter --model google/gemini-3-flash-preview --retries inf
```

What each is for:

- **collatz_level_contraction** — the mixing rate is measured at 0.81 to 0.87 per
  level and nothing forces it. This asks for the quantity that does.
- **collatz_open_arm** — the repaired words verdict B and stay B, and B is where
  the arm is. This asks what closes it and what the closure costs.
- **collatz_two_readings** — forward leaves density 0.9659^k of classes and banks
  nothing; backward certifies (4/3)^k inside [1, 2^k] and banks everything. This
  asks for the object that holds both and what is conserved across them.
