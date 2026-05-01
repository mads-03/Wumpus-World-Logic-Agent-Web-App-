Wumpus World — Logic Agent (Web App)

A web-based Dynamic Wumpus World agent that uses Propositional Logic and Resolution Refutation to deduce safe cells, navigate the grid, and locate the gold.

FEATURES
- Dynamic grid size and pit count
- Random placement of pits, Wumpus, and gold
- Percepts: Breeze, Stench, Glitter
- Propositional Logic KB (CNF)
- Resolution refutation engine
- Safe / Unknown / Danger visualization
- Inference log + metrics dashboard
- Manual step or auto-run

PROJECT STRUCTURE
index.html
style.css
agent.js
README.txt

HOW TO RUN (LOCAL)
Open index.html in a browser.

DEPLOYMENT
Vercel (recommended)
1. Push this repo to GitHub.
2. Go to https://vercel.com → New Project → Import repo
3. Framework: Other
4. Build command: None
5. Output directory: /
6. Deploy

GitHub Pages
1. Go to Repo → Settings → Pages
2. Source: main / root
3. Save and wait for URL

LOGIC DETAILS
The agent maintains a CNF Knowledge Base.
When it perceives a breeze or stench, it adds:

- B_r_c ↔ (P_n1 ∨ P_n2 ∨ …)
- S_r_c ↔ (W_n1 ∨ W_n2 ∨ …)

It uses resolution refutation to prove:
- Safe: ¬P_r_c AND ¬W_r_c
- Dangerous: P_r_c OR W_r_c

REQUIREMENTS COVERED
- Dynamic grid sizing
- Random hazards
- Percepts (Breeze/Stench)
- Propositional KB + CNF
- Resolution refutation
- Web UI + metrics
