/*
 ============================================================================
  APRIORI BASKET FINDER  -  script.js
 ============================================================================

  WHAT DOES THIS PROGRAM DO?
  --------------------------
  Imagine a grocery shop. Every customer walks out with a basket of items.
  The shop owner writes each basket on a slip of paper (that slip is called a
  "transaction"). After many customers, the owner asks:

      "Which items are often bought TOGETHER?"

  A group of items bought together is called an ITEMSET.
  An itemset is called FREQUENT when it appears in at least a certain number
  of baskets. That number is the MINIMUM SUPPORT COUNT (you choose it).

  Example: minimum support count = 40
      {Bread, Milk} appears in 63 baskets  ->  63 >= 40  ->  FREQUENT
      {Bread, Soap} appears in 7 baskets   ->   7 <  40  ->  NOT frequent

  THE APRIORI TRICK (the one big idea)
  ------------------------------------
  "If a group of items is NOT frequent, then any bigger group that contains it
   can NOT be frequent either."

  Example: if {Bread, Soap} is rare, then {Bread, Soap, Milk} must be rare too
  (it can never appear MORE often than {Bread, Soap}). So we can skip it
  without even counting. That saves a lot of work!

  THE STEPS (called "passes")
  ---------------------------
  Pass 1 : Count every single item. Keep the frequent ones      -> L1
  Pass 2 : Join frequent items into pairs, count them, keep     -> L2
  Pass 3 : Join frequent pairs into triples, count, keep        -> L3
  ... and so on, until no new frequent itemsets are found.

  In each pass (from pass 2 onward) we do 4 small things:
      a) JOIN   - glue two frequent itemsets together to make a bigger candidate
      b) PRUNE  - throw away candidates that have a non-frequent piece inside
      c) COUNT  - look through all the baskets and count the survivors
      d) KEEP   - keep only the candidates whose count >= minimum support

 

  FILE MAP (scroll to find each part)
  -----------------------------------
  PART 1 : Small helper tools
  PART 2 : The Apriori algorithm itself       <-- the heart of the project
  PART 3 : Printing results in the terminal
  PART 4 : Drawing results on the web page
  PART 5 : The database (520 grocery transactions)
  PART 6 : Start button - decides terminal or browser
 ============================================================================
*/

"use strict"; // Asks JavaScript to be strict, so silly mistakes become errors.


/* ==========================================================================
   SETTINGS you can change
   ========================================================================== */

// The minimum support count used when you do not type one yourself.
const DEFAULT_MIN_SUPPORT = 104;

// Safety brake: if one pass makes more candidates than this, we stop early.
// (A very small minimum support, like 1 or 2, can create millions of
//  candidates and freeze the computer. This number prevents that.)
const MAX_CANDIDATES_PER_PASS = 100000;


/* ==========================================================================
   PART 1 : SMALL HELPER TOOLS
   Tiny functions that the rest of the code uses again and again.
   ========================================================================== */

// Returns "what time is it now" in milliseconds.
// We call it twice (before and after) to measure how long Apriori took.
function nowInMs() {
  // "performance.now()" is the precise clock. Both Node.js and browsers have it.
  if (typeof performance !== "undefined" && performance.now) {
    return performance.now();
  }
  // If for some reason it is missing, use the normal clock instead.
  return Date.now();
}

// Turns a list of items into ONE piece of text, so we can use it as a name tag.
// ["Bread", "Milk"]  ->  "Bread|Milk"
// We need this because JavaScript Sets and Maps compare text easily,
// but they do NOT compare two lists with the same content as equal.
function makeKey(items) {
  return items.join("|");
}

// Makes an itemset pretty for humans.
// ["Bread", "Milk"]  ->  "{Bread, Milk}"
function formatItems(items) {
  return "{" + items.join(", ") + "}";
}

// Turns a count into a percentage of all baskets.
// percent(63, 520)  ->  "12.1%"
function percent(count, total) {
  return ((count / total) * 100).toFixed(1) + "%";
}


/* ==========================================================================
   PART 2 : THE APRIORI ALGORITHM
   ========================================================================== */

/*
  generateCandidates(previousFrequent, k)
  ---------------------------------------
  Builds the CANDIDATE itemsets of size k from the frequent itemsets of
  size k-1.  (A "candidate" = an itemset we THINK might be frequent; we have
  not counted it yet.)

  It does the JOIN step and the PRUNE step.

  JOIN  : two (k-1)-itemsets can be glued if everything is the same except the
          very last item.
              {Bread, Eggs}  +  {Bread, Milk}   ->  {Bread, Eggs, Milk}
              (first item "Bread" is shared, last items "Eggs" and "Milk" differ)

  PRUNE : the new candidate is thrown away if ANY of its smaller sub-groups
          is not frequent  (this is the Apriori trick from the top of the file).
              {Bread, Eggs, Milk} needs {Bread, Eggs}, {Bread, Milk} AND
              {Eggs, Milk} all to be frequent. If one of them is missing, bye!

  It returns an object with 3 things:
      candidates  : the list of survivors (these will be counted)
      joinedCount : how many we built in the JOIN step (before pruning)
      prunedCount : how many the PRUNE step threw away
*/
function generateCandidates(previousFrequent, k) {
  // Collect just the item lists, and put them in alphabetical order.
  // Sorted order lets us stop looking early (see the "break" below).
  const sortedLists = previousFrequent
    .map(function (entry) { return entry.items; })
    .sort(function (a, b) { return makeKey(a) < makeKey(b) ? -1 : 1; });

  // A quick "phone book" of every frequent (k-1)-itemset.
  // We use it to ask "is this smaller group frequent?" in an instant.
  const previousKeys = new Set(sortedLists.map(makeKey));

  const candidates = [];   // the survivors
  let joinedCount = 0;     // how many were built
  let prunedCount = 0;     // how many were thrown away
  const prefixLength = k - 2; // how many leading items must be identical

  // Compare every itemset (i) with the itemsets that come after it (j).
  for (let i = 0; i < sortedLists.length; i++) {
    for (let j = i + 1; j < sortedLists.length; j++) {
      const first = sortedLists[i];
      const second = sortedLists[j];

      // JOIN CHECK: are the leading items (all except the last) identical?
      let samePrefix = true;
      for (let p = 0; p < prefixLength; p++) {
        if (first[p] !== second[p]) {
          samePrefix = false;
          break;
        }
      }

      // The list is sorted, so once the prefix is different for this "second",
      // it will be different for all the ones after it too. Stop early!
      if (!samePrefix) {
        break;
      }

      // JOIN: glue them. Take everything from "first" and add the last item
      // of "second". (Sorted order guarantees the last items are different.)
      const newCandidate = first.concat(second[second.length - 1]);
      joinedCount++;

      // Safety brake so a tiny minimum support cannot freeze the computer.
      if (joinedCount > MAX_CANDIDATES_PER_PASS) {
        return { candidates: candidates, joinedCount: joinedCount, prunedCount: prunedCount, tooMany: true };
      }

      // PRUNE CHECK: remove one item at a time and ask the phone book
      // "was that smaller group frequent?"
      let allSubsetsFrequent = true;
      for (let removeIndex = 0; removeIndex < newCandidate.length; removeIndex++) {
        const smallerGroup = newCandidate.filter(function (item, index) {
          return index !== removeIndex;
        });
        if (!previousKeys.has(makeKey(smallerGroup))) {
          allSubsetsFrequent = false; // found a non-frequent piece
          break;
        }
      }

      if (allSubsetsFrequent) {
        candidates.push(newCandidate); // survived!
      } else {
        prunedCount++;                 // thrown away
      }
    }
  }

  return { candidates: candidates, joinedCount: joinedCount, prunedCount: prunedCount, tooMany: false };
}


/*
  runApriori(allTransactions, minSupportCount)
  --------------------------------------------
  The main function. Give it the baskets and the minimum support count,
  and it gives back ALL frequent itemsets plus lots of statistics.

  It returns:
      levels    : a list of lists.  levels[0] = frequent 1-itemsets,
                  levels[1] = frequent 2-itemsets, and so on.
                  Each entry looks like { items: ["Bread","Milk"], count: 63 }
      passStats : one small report per pass (how many candidates, etc.)
      stats     : the overall numbers (time, totals, ...)
*/
function runApriori(allTransactions, minSupportCount) {
  const startTime = nowInMs(); // start the stopwatch

  // ---- Get ready -----------------------------------------------------------
  // Turn each basket into a Set. A Set answers "is Milk in this basket?"
  // very quickly, which makes counting much faster.
  const basketSets = allTransactions.map(function (transaction) {
    return new Set(transaction.items);
  });

  const levels = [];      // the answer: frequent itemsets, grouped by size
  const passStats = [];   // a small report for each pass
  let databaseScans = 0;  // how many times we walked through all the baskets
  let totalJoined = 0;    // total candidates built by JOIN
  let totalPruned = 0;    // total candidates removed by PRUNE
  let totalCounted = 0;   // total candidates we actually had to count
  let stoppedEarly = false; // true if the safety brake was used

  // ---- PASS 1 : count every single item -----------------------------------
  const itemCounts = new Map(); // item name -> how many baskets contain it
  allTransactions.forEach(function (transaction) {
    transaction.items.forEach(function (item) {
      itemCounts.set(item, (itemCounts.get(item) || 0) + 1);
    });
  });
  databaseScans++; // we walked through the whole database once

  // Keep only the items whose count reaches the minimum support count.
  let currentFrequent = [];
  itemCounts.forEach(function (count, item) {
    if (count >= minSupportCount) {
      currentFrequent.push({ items: [item], count: count });
    }
  });

  passStats.push({
    k: 1,
    joined: itemCounts.size,   // in pass 1 every different item is a candidate
    pruned: 0,                 // nothing to prune in pass 1
    counted: itemCounts.size,
    frequent: currentFrequent.length
  });
  totalCounted += itemCounts.size;

  // ---- PASS 2, 3, 4 ... : repeat until nothing new is frequent -------------
  let k = 1;
  while (currentFrequent.length > 0) {
    // Save the frequent itemsets we just found (biggest count first).
    currentFrequent.sort(function (a, b) { return b.count - a.count; });
    levels.push(currentFrequent);

    // Now try to build bigger itemsets (size k+1).
    k++;

    // a) JOIN + b) PRUNE
    const made = generateCandidates(currentFrequent, k);
    totalJoined += made.joinedCount;
    totalPruned += made.prunedCount;

    if (made.tooMany) {
      stoppedEarly = true; // too many candidates; use the safety brake
      passStats.push({ k: k, joined: made.joinedCount, pruned: made.prunedCount, counted: 0, frequent: 0 });
      break;
    }

    // No candidates left? Then there is nothing more to find.
    if (made.candidates.length === 0) {
      passStats.push({ k: k, joined: made.joinedCount, pruned: made.prunedCount, counted: 0, frequent: 0 });
      break;
    }

    // c) COUNT: walk through every basket and, for every candidate,
    //    check whether ALL of its items are inside that basket.
    const candidateCounts = new Array(made.candidates.length).fill(0);
    basketSets.forEach(function (basket) {
      made.candidates.forEach(function (candidate, index) {
        let allInside = true;
        for (let n = 0; n < candidate.length; n++) {
          if (!basket.has(candidate[n])) {
            allInside = false;
            break; // one missing item is enough to say "no"
          }
        }
        if (allInside) {
          candidateCounts[index]++; // this basket contains the whole candidate
        }
      });
    });
    databaseScans++;
    totalCounted += made.candidates.length;

    // d) KEEP: only candidates with count >= minimum support survive.
    const nextFrequent = [];
    made.candidates.forEach(function (candidate, index) {
      if (candidateCounts[index] >= minSupportCount) {
        nextFrequent.push({ items: candidate, count: candidateCounts[index] });
      }
    });

    passStats.push({
      k: k,
      joined: made.joinedCount,
      pruned: made.prunedCount,
      counted: made.candidates.length,
      frequent: nextFrequent.length
    });

    // The new frequent itemsets become the starting point of the next pass.
    currentFrequent = nextFrequent;
  }

  // ---- Final numbers -------------------------------------------------------
  let totalFrequent = 0;
  levels.forEach(function (level) { totalFrequent += level.length; });

  let totalItemsBought = 0;
  allTransactions.forEach(function (t) { totalItemsBought += t.items.length; });

  const stats = {
    numTransactions: allTransactions.length,
    numUniqueItems: itemCounts.size,
    averageBasketSize: totalItemsBought / allTransactions.length,
    minSupportCount: minSupportCount,
    minSupportPercent: (minSupportCount / allTransactions.length) * 100,
    totalFrequent: totalFrequent,
    largestSize: levels.length,   // size of the biggest frequent itemset
    passes: passStats.length,
    databaseScans: databaseScans,
    totalJoined: totalJoined,
    totalPruned: totalPruned,
    totalCounted: totalCounted,
    stoppedEarly: stoppedEarly,
    timeMs: nowInMs() - startTime // stop the stopwatch
  };

  return { levels: levels, passStats: passStats, stats: stats };
}


/* ==========================================================================
   PART 3 : PRINTING RESULTS IN THE TERMINAL
   ========================================================================== */

// Adds spaces on the right so columns line up.   padRight("ab", 5) -> "ab   "
function padRight(text, width) {
  text = String(text);
  while (text.length < width) { text += " "; }
  return text;
}

// Adds spaces on the left so numbers line up.    padLeft("7", 4) -> "   7"
function padLeft(text, width) {
  text = String(text);
  while (text.length < width) { text = " " + text; }
  return text;
}

// Prints everything about one Apriori run to the terminal.
function printToTerminal(result) {
  const s = result.stats;
  const line = "=".repeat(64);
  const thinLine = "-".repeat(64);

  console.log("\n" + line);
  console.log("  APRIORI BASKET FINDER  -  frequent itemsets in grocery data");
  console.log(line);

  // --- The input ---
  console.log("\n[ INPUT ]");
  console.log("  Transactions (baskets)    : " + s.numTransactions);
  console.log("  Different grocery items   : " + s.numUniqueItems);
  console.log("  Average items per basket  : " + s.averageBasketSize.toFixed(2));
  console.log("  Minimum support count     : " + s.minSupportCount +
              "  (" + s.minSupportPercent.toFixed(1) + "% of all baskets)");

  // --- What happened in each pass ---
  console.log("\n[ PASS BY PASS ]");
  console.log("  " + padRight("Pass", 6) + padLeft("Joined", 9) + padLeft("Pruned", 9) +
              padLeft("Counted", 10) + padLeft("Frequent", 10));
  console.log("  " + thinLine.slice(0, 44));
  result.passStats.forEach(function (p) {
    console.log("  " + padRight("L" + p.k, 6) + padLeft(p.joined, 9) + padLeft(p.pruned, 9) +
                padLeft(p.counted, 10) + padLeft(p.frequent, 10));
  });
  console.log("  (Joined = candidates built, Pruned = thrown away by the Apriori trick,");
  console.log("   Counted = candidates checked against the baskets, Frequent = kept)");

  // --- The frequent itemsets themselves ---
  console.log("\n[ FREQUENT ITEMSETS ]");
  result.levels.forEach(function (level, index) {
    const size = index + 1;
    console.log("\n  Size " + size + "  -  " + level.length + " frequent itemset(s)");
    console.log("  " + thinLine);
    level.forEach(function (entry) {
      console.log("  " + padRight(formatItems(entry.items), 46) +
                  padLeft(entry.count, 5) + " baskets" +
                  padLeft(percent(entry.count, s.numTransactions), 8));
    });
  });

  // --- Overall numbers ---
  console.log("\n" + line);
  console.log("[ STATS ]");
  console.log("  Total frequent itemsets   : " + s.totalFrequent);
  console.log("  Largest itemset size      : " + s.largestSize);
  console.log("  Passes made               : " + s.passes);
  console.log("  Database scans            : " + s.databaseScans);
  console.log("  Candidates joined         : " + s.totalJoined);
  console.log("  Candidates pruned         : " + s.totalPruned);
  console.log("  Candidates counted        : " + s.totalCounted);
  console.log("  Time taken                : " + s.timeMs.toFixed(2) + " ms");
  if (s.stoppedEarly) {
    console.log("\n  WARNING: stopped early because there were too many candidates.");
    console.log("  Try a bigger minimum support count.");
  }
  console.log(line + "\n");
}


/* ==========================================================================
   PART 4 : DRAWING RESULTS ON THE WEB PAGE
   Everything in this part only runs inside a browser (it needs "document").
   ========================================================================== */

// Never show more than this many itemset tags at once (keeps the page fast).
const MAX_TAGS_SHOWN = 500;

function setupBrowserPage() {
  // A short way to say "find the HTML element with this id".
  function byId(id) { return document.getElementById(id); }

  // A short way to make a new HTML element with a class name and some text.
  function makeElement(tagName, className, text) {
    const element = document.createElement(tagName);
    if (className) { element.className = className; }
    if (text !== undefined) { element.textContent = text; }
    return element;
  }

  // ---- Grab the pieces of the page we need ----
  const numberBox = byId("minSupportNumber");
  const slider = byId("minSupportRange");
  const percentLabel = byId("supportPercentLabel");
  const runButton = byId("runButton");
  const errorBox = byId("errorMessage");
  const statsList = byId("statsList");
  const passBody = byId("passTableBody");
  const tabsBox = byId("levelTabs");
  const searchBox = byId("itemsetSearch");
  const itemsetList = byId("itemsetList");
  const itemsetNote = byId("itemsetNote");
  const databaseBody = byId("databaseBody");
  const databaseTitle = byId("databaseTitle");

  const total = transactions.length;

  // These "remember" things between clicks.
  let lastResult = null;  // the most recent Apriori answer
  let activeLevel = 0;    // 0 = show all sizes, 2 = show only pairs, ...

  // ---- Set up the controls ----
  slider.min = 1;
  slider.max = total;
  slider.value = DEFAULT_MIN_SUPPORT;
  numberBox.min = 1;
  numberBox.max = total;
  numberBox.value = DEFAULT_MIN_SUPPORT;

  // Shows "= 7.7% of 520 baskets" next to the number.
  function updatePercentLabel() {
    const value = Number(numberBox.value);
    if (value >= 1) {
      percentLabel.textContent = "= " + percent(value, total) + " of " + total + " baskets";
    } else {
      percentLabel.textContent = "";
    }
  }

  // Reads the minimum support count the user typed. Returns null if it is bad.
  function readMinSupport() {
    const value = Number(numberBox.value);
    const isWholeNumber = Number.isInteger(value);
    if (!isWholeNumber || value < 1 || value > total) {
      errorBox.textContent = "Enter a whole number from 1 to " + total + ".";
      return null;
    }
    errorBox.textContent = "";
    return value;
  }

  // ---- Draw the stats list ----
  function drawStats(stats) {
    statsList.innerHTML = "";
    const rows = [
      ["Frequent itemsets", stats.totalFrequent],
      ["Largest itemset size", stats.largestSize],
      ["Passes", stats.passes],
      ["Database scans", stats.databaseScans],
      ["Candidates joined", stats.totalJoined],
      ["Candidates pruned", stats.totalPruned],
      ["Candidates counted", stats.totalCounted],
      ["Different items", stats.numUniqueItems],
      ["Average basket size", stats.averageBasketSize.toFixed(2)],
      ["Time taken", stats.timeMs.toFixed(2) + " ms"]
    ];
    rows.forEach(function (row) {
      const wrapper = makeElement("div", "stat-row");
      wrapper.appendChild(makeElement("dt", "", row[0]));
      wrapper.appendChild(makeElement("dd", "", String(row[1])));
      statsList.appendChild(wrapper);
    });
  }

  // ---- Draw the pass-by-pass table ----
  function drawPasses(passStats) {
    passBody.innerHTML = "";
    passStats.forEach(function (p) {
      const tr = makeElement("tr");
      [("L" + p.k), p.joined, p.pruned, p.counted, p.frequent].forEach(function (cell) {
        tr.appendChild(makeElement("td", "", String(cell)));
      });
      passBody.appendChild(tr);
    });
  }

  // ---- Draw the tab buttons: "All sizes", "Size 1", "Size 2", ... ----
  function drawTabs(levels) {
    tabsBox.innerHTML = "";

    function addTab(label, levelNumber) {
      const button = makeElement("button", "tab", label);
      button.type = "button";
      button.setAttribute("aria-pressed", activeLevel === levelNumber ? "true" : "false");
      button.addEventListener("click", function () {
        activeLevel = levelNumber;
        drawTabs(lastResult.levels);
        drawItemsets();
      });
      tabsBox.appendChild(button);
    }

    addTab("All sizes", 0);
    levels.forEach(function (level, index) {
      addTab("Size " + (index + 1) + " (" + level.length + ")", index + 1);
    });
  }

  // ---- Draw the itemset tags ----
  function drawItemsets() {
    itemsetList.innerHTML = "";
    if (!lastResult) { return; }

    // 1) Collect itemsets from the chosen size (or from all sizes).
    let everything = [];
    lastResult.levels.forEach(function (level, index) {
      if (activeLevel === 0 || activeLevel === index + 1) {
        everything = everything.concat(level);
      }
    });

    // 2) Keep only the ones that match the search words.
    const searchText = searchBox.value.trim().toLowerCase();
    if (searchText !== "") {
      everything = everything.filter(function (entry) {
        return entry.items.join(" ").toLowerCase().indexOf(searchText) !== -1;
      });
    }

    // 3) Biggest count first.
    everything.sort(function (a, b) { return b.count - a.count; });

    // 4) Cut the list if it is too long for the page.
    const shown = everything.slice(0, MAX_TAGS_SHOWN);

    if (everything.length === 0) {
      itemsetNote.textContent = lastResult.stats.totalFrequent === 0
        ? "No itemset reaches this minimum support. Lower the count and run again."
        : "No itemset matches your search.";
      return;
    }
    itemsetNote.textContent = everything.length > shown.length
      ? "Showing the top " + shown.length + " of " + everything.length + ". Search or raise the minimum support to narrow it down."
      : everything.length + " itemset" + (everything.length === 1 ? "" : "s") + ", most frequent first.";

    // 5) Make one "price tag" for each itemset.
    const biggestCount = shown[0].count;
    shown.forEach(function (entry) {
      const tag = makeElement("li", "tag");

      const names = makeElement("div", "tag-items");
      entry.items.forEach(function (item) {
        names.appendChild(makeElement("span", "chip", item));
      });

      const price = makeElement("div", "tag-count");
      price.appendChild(makeElement("strong", "", String(entry.count)));
      price.appendChild(makeElement("span", "", percent(entry.count, total)));

      // A thin bar whose length shows how common the itemset is.
      const bar = makeElement("div", "bar");
      const fill = makeElement("div", "bar-fill");
      fill.style.width = ((entry.count / biggestCount) * 100) + "%";
      bar.appendChild(fill);

      tag.appendChild(names);
      tag.appendChild(price);
      tag.appendChild(bar);
      itemsetList.appendChild(tag);
    });
  }

  // ---- Run Apriori and update the whole page ----
  function runAndDraw() {
    const minSupport = readMinSupport();
    if (minSupport === null) { return; } // bad input -> do nothing

    lastResult = runApriori(transactions, minSupport);

    // If the old tab no longer exists (for example "Size 4"), go back to "All".
    if (activeLevel > lastResult.levels.length) { activeLevel = 0; }

    drawStats(lastResult.stats);
    drawPasses(lastResult.passStats);
    drawTabs(lastResult.levels);
    drawItemsets();

    // Warn the user if the safety brake was used.
    if (lastResult.stats.stoppedEarly) {
      errorBox.textContent = "Stopped early: too many candidates. Use a bigger minimum support count.";
    }

    // Also print the same report in the browser console (press F12 to see it).
    printToTerminal(lastResult);
  }

  // ---- Fill the database viewer (the table of all baskets) ----
  databaseTitle.textContent = "View the database (" + total + " transactions)";
  transactions.forEach(function (transaction) {
    const tr = makeElement("tr");
    tr.appendChild(makeElement("td", "", transaction.id));
    tr.appendChild(makeElement("td", "", String(transaction.items.length)));
    tr.appendChild(makeElement("td", "", transaction.items.join(", ")));
    databaseBody.appendChild(tr);
  });

  // ---- Connect the controls to the code ----
  // Moving the slider updates the number box (and the percentage label).
  slider.addEventListener("input", function () {
    numberBox.value = slider.value;
    updatePercentLabel();
  });
  // Letting go of the slider runs Apriori with the new value.
  slider.addEventListener("change", runAndDraw);

  // Typing a number moves the slider and updates the label.
  numberBox.addEventListener("input", function () {
    slider.value = numberBox.value;
    updatePercentLabel();
  });
  // Pressing Enter inside the number box runs Apriori.
  numberBox.addEventListener("keydown", function (event) {
    if (event.key === "Enter") { runAndDraw(); }
  });

  runButton.addEventListener("click", runAndDraw);
  searchBox.addEventListener("input", drawItemsets);

  // ---- First run when the page opens ----
  updatePercentLabel();
  runAndDraw();
}


/* ==========================================================================
   PART 5 : THE DATABASE
   520 grocery transactions. Each one is an object with:
       id    : the transaction number (like a receipt number)
       items : the grocery items in that customer's basket
   The data is written out in full (not random), so you get the same
   answers every time you run the program.
   ========================================================================== */

const transactions = [
  { id: "T001", items: ["Cooking Oil", "Garlic", "Onion", "Rice", "Salt", "Spices", "Tea", "Yogurt"] },
  { id: "T002", items: ["Chicken", "Garlic", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T003", items: ["Cooking Oil", "Garlic", "Lentils", "Noodles", "Onion", "Salt", "Spices"] },
  { id: "T004", items: ["Butter", "Eggs", "Flour", "Sugar", "Tomato"] },
  { id: "T005", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T006", items: ["Chips", "Fish", "Onion", "Rice", "Spices", "Sugar", "Tomato", "Toothpaste"] },
  { id: "T007", items: ["Lentils", "Milk", "Soap", "Toothpaste", "Yogurt"] },
  { id: "T008", items: ["Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T009", items: ["Flour", "Yogurt"] },
  { id: "T010", items: ["Cooking Oil", "Onion", "Rice", "Spices"] },
  { id: "T011", items: ["Chocolate", "Noodles", "Toothpaste"] },
  { id: "T012", items: ["Apples", "Bananas", "Chicken", "Flour", "Juice", "Milk", "Yogurt"] },
  { id: "T013", items: ["Chicken", "Coffee", "Garlic", "Potato", "Spices", "Tomato", "Yogurt"] },
  { id: "T014", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T015", items: ["Bread", "Butter", "Milk"] },
  { id: "T016", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T017", items: ["Biscuits", "Butter", "Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Soap", "Spices"] },
  { id: "T018", items: ["Cheese", "Flour", "Yogurt"] },
  { id: "T019", items: ["Apples", "Bananas", "Oranges"] },
  { id: "T020", items: ["Butter", "Eggs", "Fish", "Flour", "Sugar"] },
  { id: "T021", items: ["Biscuits", "Milk", "Sugar", "Tea", "Toothpaste"] },
  { id: "T022", items: ["Chicken", "Garlic", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T023", items: ["Eggs", "Shampoo"] },
  { id: "T024", items: ["Apples", "Bananas", "Garlic", "Juice", "Noodles", "Oranges"] },
  { id: "T025", items: ["Apples", "Bananas", "Juice", "Oranges"] },
  { id: "T026", items: ["Butter", "Chips", "Chocolate", "Juice", "Noodles"] },
  { id: "T027", items: ["Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T028", items: ["Biscuits", "Garlic", "Lentils", "Oranges", "Rice", "Salt", "Soap", "Spices"] },
  { id: "T029", items: ["Chicken", "Garlic", "Onion", "Potato", "Shampoo", "Tomato"] },
  { id: "T030", items: ["Potato", "Shampoo", "Soap"] },
  { id: "T031", items: ["Fish", "Flour", "Onion", "Potato", "Rice", "Tomato"] },
  { id: "T032", items: ["Chips", "Chocolate", "Juice", "Noodles", "Onion"] },
  { id: "T033", items: ["Bananas", "Chicken", "Garlic", "Onion", "Potato", "Soap", "Spices", "Tomato"] },
  { id: "T034", items: ["Biscuits", "Milk", "Shampoo", "Soap", "Sugar", "Toothpaste"] },
  { id: "T035", items: ["Apples", "Bananas", "Bread", "Juice", "Oranges"] },
  { id: "T036", items: ["Biscuits", "Cheese", "Milk", "Salt", "Soap", "Sugar", "Tea"] },
  { id: "T037", items: ["Biscuits", "Milk", "Onion", "Sugar"] },
  { id: "T038", items: ["Chicken", "Potato", "Spices"] },
  { id: "T039", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T040", items: ["Butter", "Chips", "Eggs", "Flour", "Sugar"] },
  { id: "T041", items: ["Chips", "Chocolate", "Juice", "Noodles"] },
  { id: "T042", items: ["Apples", "Milk", "Sugar", "Tea", "Toothpaste"] },
  { id: "T043", items: ["Bananas", "Fish", "Oranges", "Soap", "Toothpaste"] },
  { id: "T044", items: ["Butter", "Milk"] },
  { id: "T045", items: ["Bread", "Butter", "Eggs", "Garlic", "Lentils", "Milk", "Onion", "Rice", "Salt", "Spices", "Yogurt"] },
  { id: "T046", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Salt", "Spices"] },
  { id: "T047", items: ["Apples", "Bananas", "Juice", "Oranges", "Soap", "Yogurt"] },
  { id: "T048", items: ["Shampoo", "Soap", "Spices", "Toothpaste"] },
  { id: "T049", items: ["Biscuits", "Cheese", "Chicken", "Garlic", "Milk", "Onion", "Potato", "Spices", "Tea", "Tomato"] },
  { id: "T050", items: ["Bananas", "Bread", "Butter", "Eggs", "Milk"] },
  { id: "T051", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Sugar"] },
  { id: "T052", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Salt", "Spices", "Toothpaste"] },
  { id: "T053", items: ["Bread", "Butter", "Cooking Oil", "Eggs", "Garlic", "Lentils", "Milk", "Rice", "Salt", "Spices"] },
  { id: "T054", items: ["Bread", "Butter", "Eggs", "Milk", "Onion"] },
  { id: "T055", items: ["Cheese", "Cooking Oil", "Lentils", "Onion", "Rice", "Salt", "Spices", "Toothpaste"] },
  { id: "T056", items: ["Cooking Oil", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T057", items: ["Butter", "Cooking Oil", "Garlic", "Lentils", "Onion", "Salt", "Spices"] },
  { id: "T058", items: ["Apples", "Cooking Oil", "Fish", "Garlic", "Juice", "Lentils", "Onion", "Salt", "Spices"] },
  { id: "T059", items: ["Chicken", "Coffee", "Onion", "Oranges", "Potato", "Rice", "Spices", "Tomato", "Yogurt"] },
  { id: "T060", items: ["Apples", "Bananas", "Coffee", "Cooking Oil", "Juice", "Oranges"] },
  { id: "T061", items: ["Chicken", "Garlic", "Onion", "Soap", "Spices", "Tomato", "Toothpaste"] },
  { id: "T062", items: ["Bananas", "Bread", "Butter", "Eggs", "Milk", "Onion"] },
  { id: "T063", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T064", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Salt"] },
  { id: "T065", items: ["Cooking Oil", "Garlic", "Lentils", "Salt", "Sugar"] },
  { id: "T066", items: ["Cooking Oil", "Garlic", "Lentils", "Rice", "Salt"] },
  { id: "T067", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T068", items: ["Apples", "Butter", "Eggs", "Milk"] },
  { id: "T069", items: ["Bread", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T070", items: ["Apples", "Bananas", "Cooking Oil", "Garlic", "Juice", "Lentils", "Onion", "Oranges", "Salt", "Spices"] },
  { id: "T071", items: ["Coffee", "Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T072", items: ["Cooking Oil", "Onion", "Potato", "Rice", "Salt", "Spices"] },
  { id: "T073", items: ["Biscuits", "Chips", "Chocolate", "Juice", "Noodles", "Sugar", "Tea"] },
  { id: "T074", items: ["Chicken", "Garlic", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T075", items: ["Butter", "Eggs", "Flour", "Sugar"] },
  { id: "T076", items: ["Shampoo", "Soap", "Toothpaste"] },
  { id: "T077", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T078", items: ["Apples", "Bananas", "Biscuits", "Bread", "Butter", "Eggs", "Milk"] },
  { id: "T079", items: ["Cheese", "Fish", "Milk", "Onion", "Rice", "Spices", "Tomato"] },
  { id: "T080", items: ["Biscuits", "Juice", "Milk", "Sugar", "Yogurt"] },
  { id: "T081", items: ["Biscuits", "Chicken", "Garlic", "Milk", "Onion", "Potato", "Soap", "Spices", "Sugar", "Tea", "Tomato"] },
  { id: "T082", items: ["Apples", "Bananas", "Juice", "Oranges"] },
  { id: "T083", items: ["Chicken", "Cooking Oil", "Garlic", "Lentils", "Onion", "Potato", "Rice", "Salt", "Spices", "Tomato"] },
  { id: "T084", items: ["Apples", "Bananas", "Fish", "Oranges"] },
  { id: "T085", items: ["Eggs", "Garlic", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T086", items: ["Cooking Oil", "Garlic", "Lentils", "Noodles", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T087", items: ["Chicken", "Cooking Oil", "Garlic", "Lentils", "Noodles", "Onion", "Potato", "Rice", "Spices", "Tomato"] },
  { id: "T088", items: ["Bread", "Butter", "Chips", "Eggs", "Oranges", "Shampoo", "Soap"] },
  { id: "T089", items: ["Bread", "Butter", "Eggs", "Lentils", "Milk", "Shampoo"] },
  { id: "T090", items: ["Cheese", "Flour", "Milk", "Onion", "Yogurt"] },
  { id: "T091", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Potato", "Rice", "Salt", "Spices"] },
  { id: "T092", items: ["Apples", "Juice", "Milk", "Oranges", "Shampoo"] },
  { id: "T093", items: ["Bread", "Butter", "Milk"] },
  { id: "T094", items: ["Cooking Oil", "Garlic", "Onion", "Salt", "Spices"] },
  { id: "T095", items: ["Biscuits", "Milk", "Sugar", "Tea"] },
  { id: "T096", items: ["Cooking Oil", "Garlic", "Onion", "Rice", "Salt"] },
  { id: "T097", items: ["Cooking Oil", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T098", items: ["Bread", "Coffee", "Eggs"] },
  { id: "T099", items: ["Apples", "Juice", "Oranges", "Rice"] },
  { id: "T100", items: ["Fish", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices", "Tomato"] },
  { id: "T101", items: ["Cheese", "Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt"] },
  { id: "T102", items: ["Chicken", "Eggs", "Garlic", "Milk", "Onion", "Potato", "Spices", "Sugar", "Tomato"] },
  { id: "T103", items: ["Chocolate", "Lentils", "Onion", "Salt", "Spices"] },
  { id: "T104", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Oranges", "Rice", "Shampoo", "Spices", "Tea"] },
  { id: "T105", items: ["Chips", "Chocolate", "Juice", "Noodles", "Spices"] },
  { id: "T106", items: ["Onion", "Potato", "Shampoo", "Spices", "Tomato"] },
  { id: "T107", items: ["Butter", "Eggs", "Flour", "Sugar"] },
  { id: "T108", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Salt", "Spices"] },
  { id: "T109", items: ["Biscuits", "Garlic", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T110", items: ["Fish", "Flour", "Onion", "Rice", "Tea", "Tomato"] },
  { id: "T111", items: ["Butter", "Chips", "Cooking Oil", "Eggs", "Garlic", "Milk", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T112", items: ["Biscuits", "Cooking Oil", "Garlic", "Lentils", "Milk", "Onion", "Rice", "Salt", "Spices", "Sugar", "Tea"] },
  { id: "T113", items: ["Bread", "Butter", "Chicken", "Eggs", "Milk", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T114", items: ["Biscuits", "Flour", "Milk", "Sugar", "Tea"] },
  { id: "T115", items: ["Biscuits", "Bread", "Milk", "Sugar", "Tea"] },
  { id: "T116", items: ["Garlic", "Lentils", "Milk", "Rice", "Salt", "Yogurt"] },
  { id: "T117", items: ["Apples", "Bananas", "Bread", "Butter", "Juice", "Noodles", "Oranges"] },
  { id: "T118", items: ["Biscuits", "Bread", "Butter", "Eggs", "Milk", "Potato", "Spices", "Tea"] },
  { id: "T119", items: ["Chicken", "Garlic", "Potato", "Spices", "Tomato"] },
  { id: "T120", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt"] },
  { id: "T121", items: ["Cheese", "Yogurt"] },
  { id: "T122", items: ["Bread", "Butter", "Chocolate", "Eggs", "Lentils", "Milk", "Rice"] },
  { id: "T123", items: ["Cooking Oil", "Garlic", "Lentils", "Rice", "Salt"] },
  { id: "T124", items: ["Fish", "Milk", "Onion", "Yogurt"] },
  { id: "T125", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices", "Yogurt"] },
  { id: "T126", items: ["Biscuits", "Milk", "Onion", "Rice", "Sugar", "Tea", "Tomato"] },
  { id: "T127", items: ["Chicken", "Garlic", "Lentils", "Onion", "Oranges", "Potato", "Rice", "Salt", "Spices", "Sugar"] },
  { id: "T128", items: ["Bread", "Eggs", "Milk"] },
  { id: "T129", items: ["Cheese", "Milk", "Shampoo", "Toothpaste", "Yogurt"] },
  { id: "T130", items: ["Fish", "Onion", "Soap", "Spices", "Tomato"] },
  { id: "T131", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T132", items: ["Bread", "Butter", "Cooking Oil", "Eggs", "Garlic", "Lentils", "Milk", "Onion", "Salt"] },
  { id: "T133", items: ["Bread", "Butter", "Chips", "Eggs", "Milk", "Spices"] },
  { id: "T134", items: ["Bread", "Butter", "Cooking Oil", "Eggs", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T135", items: ["Garlic", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T136", items: ["Bread", "Butter", "Eggs", "Fish", "Milk", "Onion", "Spices", "Tomato"] },
  { id: "T137", items: ["Chicken", "Garlic", "Spices", "Tomato"] },
  { id: "T138", items: ["Apples", "Bananas", "Bread", "Eggs", "Juice"] },
  { id: "T139", items: ["Garlic", "Lentils", "Onion", "Rice", "Spices"] },
  { id: "T140", items: ["Garlic", "Lentils", "Onion", "Salt", "Spices"] },
  { id: "T141", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Salt", "Soap", "Spices"] },
  { id: "T142", items: ["Bread", "Butter", "Coffee", "Cooking Oil", "Eggs", "Garlic", "Lentils", "Milk", "Noodles", "Rice", "Salt", "Soap", "Spices"] },
  { id: "T143", items: ["Biscuits", "Milk", "Salt", "Tea"] },
  { id: "T144", items: ["Apples", "Butter", "Eggs", "Flour", "Sugar"] },
  { id: "T145", items: ["Garlic", "Lentils", "Onion", "Rice", "Salt"] },
  { id: "T146", items: ["Fish", "Lentils", "Onion", "Rice", "Salt", "Spices", "Tomato"] },
  { id: "T147", items: ["Fish", "Garlic", "Onion", "Potato", "Rice", "Soap", "Spices", "Tomato"] },
  { id: "T148", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T149", items: ["Butter", "Fish", "Onion", "Rice", "Spices", "Tomato", "Toothpaste", "Yogurt"] },
  { id: "T150", items: ["Apples", "Butter", "Juice", "Oranges"] },
  { id: "T151", items: ["Chicken", "Garlic", "Spices", "Tomato"] },
  { id: "T152", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T153", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T154", items: ["Biscuits", "Chocolate", "Coffee", "Fish", "Milk", "Onion", "Spices", "Sugar", "Tea", "Tomato"] },
  { id: "T155", items: ["Biscuits", "Milk", "Sugar", "Tea", "Tomato"] },
  { id: "T156", items: ["Bread", "Butter", "Milk", "Oranges"] },
  { id: "T157", items: ["Bread", "Eggs", "Milk", "Onion", "Yogurt"] },
  { id: "T158", items: ["Apples", "Bananas", "Chicken"] },
  { id: "T159", items: ["Biscuits", "Milk", "Salt", "Sugar", "Tea"] },
  { id: "T160", items: ["Bread", "Butter", "Cooking Oil", "Eggs", "Garlic", "Lentils", "Milk", "Noodles", "Onion", "Rice", "Salt", "Soap", "Spices"] },
  { id: "T161", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T162", items: ["Apples", "Bananas", "Cooking Oil", "Garlic", "Juice", "Lentils", "Oranges", "Rice", "Salt", "Spices"] },
  { id: "T163", items: ["Bread", "Butter", "Eggs", "Juice", "Milk", "Potato"] },
  { id: "T164", items: ["Bananas", "Chicken", "Fish", "Garlic", "Onion", "Potato", "Rice", "Spices", "Tomato"] },
  { id: "T165", items: ["Garlic", "Onion", "Potato", "Shampoo", "Soap", "Spices", "Tomato", "Toothpaste"] },
  { id: "T166", items: ["Biscuits", "Milk", "Sugar", "Tea"] },
  { id: "T167", items: ["Chicken", "Garlic", "Noodles", "Onion", "Potato", "Salt", "Spices", "Tomato"] },
  { id: "T168", items: ["Apples", "Bananas", "Juice", "Oranges"] },
  { id: "T169", items: ["Cheese", "Milk", "Yogurt"] },
  { id: "T170", items: ["Cooking Oil", "Garlic", "Lentils", "Rice", "Spices"] },
  { id: "T171", items: ["Bread", "Butter", "Cooking Oil", "Eggs", "Sugar"] },
  { id: "T172", items: ["Bread", "Butter", "Flour", "Milk", "Toothpaste"] },
  { id: "T173", items: ["Apples", "Bananas", "Juice", "Lentils", "Oranges", "Sugar"] },
  { id: "T174", items: ["Butter", "Eggs", "Flour"] },
  { id: "T175", items: ["Fish", "Garlic", "Onion", "Potato", "Rice", "Spices", "Tomato"] },
  { id: "T176", items: ["Bananas", "Shampoo", "Soap", "Toothpaste"] },
  { id: "T177", items: ["Potato", "Shampoo", "Spices"] },
  { id: "T178", items: ["Fish", "Lentils", "Onion", "Rice", "Spices"] },
  { id: "T179", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T180", items: ["Apples", "Bananas", "Biscuits", "Butter", "Eggs", "Juice", "Oranges"] },
  { id: "T181", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Salt", "Spices"] },
  { id: "T182", items: ["Biscuits", "Milk", "Sugar", "Tea"] },
  { id: "T183", items: ["Biscuits", "Cooking Oil", "Garlic", "Lentils", "Onion", "Salt", "Shampoo", "Spices"] },
  { id: "T184", items: ["Chicken", "Garlic", "Onion", "Potato", "Spices", "Sugar", "Tomato"] },
  { id: "T185", items: ["Garlic", "Onion", "Potato", "Salt", "Spices", "Tomato"] },
  { id: "T186", items: ["Butter", "Chicken", "Garlic", "Juice", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T187", items: ["Fish", "Onion", "Rice", "Shampoo", "Spices", "Tomato"] },
  { id: "T188", items: ["Cheese", "Milk", "Yogurt"] },
  { id: "T189", items: ["Biscuits", "Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Spices", "Sugar"] },
  { id: "T190", items: ["Bread", "Chocolate", "Cooking Oil", "Garlic", "Lentils", "Soap"] },
  { id: "T191", items: ["Cheese", "Cooking Oil", "Garlic", "Lentils", "Milk", "Onion", "Salt", "Yogurt"] },
  { id: "T192", items: ["Eggs", "Flour"] },
  { id: "T193", items: ["Apples", "Bananas", "Juice", "Lentils", "Milk", "Oranges", "Soap", "Yogurt"] },
  { id: "T194", items: ["Bread", "Butter", "Chicken", "Eggs", "Garlic", "Onion", "Spices", "Tomato", "Yogurt"] },
  { id: "T195", items: ["Chips", "Chocolate", "Juice", "Noodles", "Tomato"] },
  { id: "T196", items: ["Cooking Oil", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T197", items: ["Biscuits", "Shampoo", "Soap", "Toothpaste"] },
  { id: "T198", items: ["Bread", "Butter", "Milk", "Onion", "Rice", "Toothpaste"] },
  { id: "T199", items: ["Butter", "Eggs", "Flour", "Garlic"] },
  { id: "T200", items: ["Bread", "Butter", "Eggs", "Garlic", "Milk", "Oranges"] },
  { id: "T201", items: ["Bread", "Butter", "Chicken", "Eggs", "Milk", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T202", items: ["Bread", "Milk", "Toothpaste", "Yogurt"] },
  { id: "T203", items: ["Milk", "Sugar", "Tea"] },
  { id: "T204", items: ["Chicken", "Chips", "Cooking Oil", "Garlic", "Lentils", "Noodles", "Onion", "Rice", "Spices", "Tomato"] },
  { id: "T205", items: ["Fish", "Onion", "Rice", "Shampoo", "Spices", "Tomato"] },
  { id: "T206", items: ["Flour", "Sugar"] },
  { id: "T207", items: ["Apples", "Bananas", "Chips", "Juice", "Noodles", "Oranges", "Potato"] },
  { id: "T208", items: ["Cheese", "Milk", "Yogurt"] },
  { id: "T209", items: ["Chips", "Juice", "Noodles", "Sugar"] },
  { id: "T210", items: ["Cooking Oil", "Lentils", "Onion", "Oranges", "Salt", "Spices"] },
  { id: "T211", items: ["Cheese", "Cooking Oil", "Eggs", "Fish", "Garlic", "Onion", "Rice", "Salt", "Spices", "Tomato"] },
  { id: "T212", items: ["Apples", "Shampoo", "Soap", "Sugar", "Toothpaste"] },
  { id: "T213", items: ["Chicken", "Garlic", "Noodles", "Onion", "Tomato"] },
  { id: "T214", items: ["Chicken", "Eggs", "Flour", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T215", items: ["Chips", "Chocolate", "Garlic", "Juice", "Noodles"] },
  { id: "T216", items: ["Biscuits", "Milk", "Spices", "Tea"] },
  { id: "T217", items: ["Chips", "Chocolate", "Juice", "Noodles", "Soap", "Toothpaste"] },
  { id: "T218", items: ["Biscuits", "Milk", "Oranges", "Sugar", "Tea"] },
  { id: "T219", items: ["Cheese", "Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T220", items: ["Apples", "Biscuits", "Garlic", "Milk", "Sugar", "Tea"] },
  { id: "T221", items: ["Biscuits", "Coffee", "Eggs", "Milk", "Potato", "Sugar", "Tea"] },
  { id: "T222", items: ["Butter", "Chicken", "Cooking Oil", "Eggs", "Flour", "Lentils", "Milk", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T223", items: ["Shampoo", "Soap", "Toothpaste"] },
  { id: "T224", items: ["Bread", "Eggs", "Milk"] },
  { id: "T225", items: ["Garlic", "Juice", "Potato", "Spices", "Tomato", "Yogurt"] },
  { id: "T226", items: ["Chicken", "Coffee", "Garlic", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T227", items: ["Cooking Oil", "Garlic", "Lentils", "Milk", "Onion", "Rice", "Salt"] },
  { id: "T228", items: ["Biscuits", "Cooking Oil", "Garlic", "Lentils", "Milk", "Onion", "Rice", "Salt", "Spices", "Sugar", "Tea"] },
  { id: "T229", items: ["Chicken", "Garlic", "Potato", "Spices", "Tomato"] },
  { id: "T230", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T231", items: ["Apples", "Bananas", "Chicken", "Flour", "Juice", "Oranges", "Tomato"] },
  { id: "T232", items: ["Chips", "Chocolate", "Eggs", "Rice", "Salt"] },
  { id: "T233", items: ["Chips", "Chocolate", "Juice", "Noodles"] },
  { id: "T234", items: ["Butter", "Eggs", "Flour", "Milk", "Soap", "Sugar"] },
  { id: "T235", items: ["Bread", "Butter", "Chips", "Eggs", "Milk"] },
  { id: "T236", items: ["Bananas", "Juice", "Noodles", "Tomato", "Toothpaste"] },
  { id: "T237", items: ["Cheese", "Milk", "Yogurt"] },
  { id: "T238", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T239", items: ["Cooking Oil", "Fish", "Garlic", "Lentils", "Onion", "Oranges", "Spices"] },
  { id: "T240", items: ["Bread", "Butter", "Eggs", "Milk", "Spices"] },
  { id: "T241", items: ["Chips", "Chocolate", "Cooking Oil", "Fish", "Garlic", "Juice", "Lentils", "Noodles", "Rice", "Salt", "Spices"] },
  { id: "T242", items: ["Onion", "Shampoo", "Soap", "Toothpaste"] },
  { id: "T243", items: ["Biscuits", "Milk", "Oranges", "Sugar", "Tea"] },
  { id: "T244", items: ["Bread", "Chicken", "Eggs"] },
  { id: "T245", items: ["Butter", "Chicken", "Cooking Oil", "Fish", "Garlic", "Lentils", "Onion", "Potato", "Rice", "Spices", "Sugar", "Tomato"] },
  { id: "T246", items: ["Biscuits", "Bread", "Butter", "Eggs", "Milk", "Salt", "Sugar", "Tea", "Tomato", "Yogurt"] },
  { id: "T247", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T248", items: ["Chicken", "Chips", "Chocolate", "Juice"] },
  { id: "T249", items: ["Fish", "Milk", "Sugar", "Tea"] },
  { id: "T250", items: ["Milk", "Sugar"] },
  { id: "T251", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T252", items: ["Bread", "Butter", "Eggs", "Milk", "Sugar"] },
  { id: "T253", items: ["Butter", "Flour"] },
  { id: "T254", items: ["Chicken", "Garlic", "Potato", "Spices", "Tea", "Tomato"] },
  { id: "T255", items: ["Butter", "Eggs", "Milk"] },
  { id: "T256", items: ["Chicken", "Garlic", "Onion", "Potato", "Spices"] },
  { id: "T257", items: ["Cheese", "Milk"] },
  { id: "T258", items: ["Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T259", items: ["Biscuits", "Juice", "Tea"] },
  { id: "T260", items: ["Biscuits", "Juice", "Milk", "Potato", "Sugar"] },
  { id: "T261", items: ["Chips", "Chocolate", "Flour", "Noodles", "Oranges"] },
  { id: "T262", items: ["Butter", "Flour"] },
  { id: "T263", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T264", items: ["Bananas", "Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T265", items: ["Butter", "Milk", "Onion"] },
  { id: "T266", items: ["Cheese", "Chicken", "Garlic", "Milk", "Onion", "Potato", "Spices", "Yogurt"] },
  { id: "T267", items: ["Biscuits", "Chips", "Chocolate", "Juice", "Noodles", "Oranges", "Shampoo", "Sugar", "Tea"] },
  { id: "T268", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T269", items: ["Bananas", "Chips", "Chocolate", "Juice", "Noodles"] },
  { id: "T270", items: ["Biscuits", "Milk", "Sugar", "Tea"] },
  { id: "T271", items: ["Bread", "Butter", "Milk"] },
  { id: "T272", items: ["Chips", "Juice", "Noodles", "Shampoo", "Soap", "Toothpaste"] },
  { id: "T273", items: ["Bread", "Butter", "Cooking Oil", "Garlic", "Milk", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T274", items: ["Chicken", "Chocolate", "Garlic", "Onion", "Potato", "Spices", "Sugar", "Tomato"] },
  { id: "T275", items: ["Apples", "Juice"] },
  { id: "T276", items: ["Soap", "Spices", "Toothpaste"] },
  { id: "T277", items: ["Apples", "Bananas", "Juice", "Noodles", "Oranges"] },
  { id: "T278", items: ["Bread", "Eggs", "Milk", "Oranges", "Yogurt"] },
  { id: "T279", items: ["Bread", "Butter", "Eggs", "Fish", "Milk", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T280", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Soap", "Spices"] },
  { id: "T281", items: ["Apples", "Bananas", "Juice", "Oranges", "Potato"] },
  { id: "T282", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T283", items: ["Chocolate", "Coffee", "Cooking Oil", "Garlic", "Rice", "Salt", "Tomato"] },
  { id: "T284", items: ["Cooking Oil", "Garlic", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T285", items: ["Cheese", "Milk", "Rice", "Soap", "Sugar", "Yogurt"] },
  { id: "T286", items: ["Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T287", items: ["Butter", "Cooking Oil", "Eggs", "Garlic", "Juice", "Lentils", "Rice", "Shampoo", "Spices", "Sugar"] },
  { id: "T288", items: ["Chicken", "Garlic", "Milk", "Onion", "Potato", "Spices", "Tomato", "Yogurt"] },
  { id: "T289", items: ["Cooking Oil", "Flour", "Garlic", "Lentils", "Onion", "Potato", "Rice", "Salt"] },
  { id: "T290", items: ["Biscuits", "Butter", "Eggs", "Flour", "Milk", "Sugar", "Tea"] },
  { id: "T291", items: ["Eggs", "Milk"] },
  { id: "T292", items: ["Bread", "Butter", "Chips", "Eggs", "Juice", "Milk", "Noodles", "Oranges", "Shampoo"] },
  { id: "T293", items: ["Milk", "Oranges", "Sugar", "Tea"] },
  { id: "T294", items: ["Apples", "Cooking Oil", "Garlic", "Lentils", "Milk", "Onion", "Oranges", "Rice", "Salt", "Spices", "Sugar", "Tea", "Tomato"] },
  { id: "T295", items: ["Biscuits", "Bread", "Chips", "Juice", "Milk", "Noodles", "Sugar", "Tea"] },
  { id: "T296", items: ["Bananas", "Chicken", "Coffee", "Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Spices"] },
  { id: "T297", items: ["Apples", "Bananas", "Bread", "Butter", "Eggs", "Juice", "Oranges"] },
  { id: "T298", items: ["Biscuits", "Cheese", "Milk", "Sugar", "Tea", "Yogurt"] },
  { id: "T299", items: ["Biscuits", "Cheese", "Chips", "Milk", "Sugar", "Yogurt"] },
  { id: "T300", items: ["Biscuits", "Milk", "Sugar", "Tea"] },
  { id: "T301", items: ["Biscuits", "Bread", "Butter", "Cooking Oil", "Eggs", "Garlic", "Lentils", "Milk", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T302", items: ["Fish", "Onion", "Rice", "Spices", "Tomato", "Toothpaste"] },
  { id: "T303", items: ["Chicken", "Cooking Oil", "Garlic", "Lentils", "Onion", "Potato", "Rice", "Salt", "Spices", "Tomato"] },
  { id: "T304", items: ["Chicken", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T305", items: ["Bread", "Butter", "Eggs", "Milk", "Potato"] },
  { id: "T306", items: ["Bananas", "Cooking Oil", "Garlic", "Juice", "Lentils", "Onion", "Oranges", "Rice", "Salt", "Spices"] },
  { id: "T307", items: ["Cooking Oil", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T308", items: ["Biscuits", "Fish", "Milk", "Onion", "Rice", "Spices", "Tea"] },
  { id: "T309", items: ["Biscuits", "Butter", "Eggs", "Flour", "Juice", "Sugar"] },
  { id: "T310", items: ["Biscuits", "Cooking Oil", "Eggs", "Flour", "Garlic", "Rice", "Salt", "Spices", "Sugar", "Toothpaste"] },
  { id: "T311", items: ["Oranges", "Shampoo", "Soap", "Toothpaste"] },
  { id: "T312", items: ["Bread", "Butter", "Eggs"] },
  { id: "T313", items: ["Biscuits", "Chicken", "Garlic", "Onion", "Potato", "Tomato"] },
  { id: "T314", items: ["Apples", "Butter", "Chicken", "Eggs", "Flour", "Garlic", "Potato", "Rice", "Spices", "Sugar"] },
  { id: "T315", items: ["Cheese", "Milk", "Sugar", "Tea"] },
  { id: "T316", items: ["Butter", "Eggs", "Milk"] },
  { id: "T317", items: ["Chips", "Chocolate", "Juice", "Noodles", "Toothpaste"] },
  { id: "T318", items: ["Shampoo", "Soap", "Toothpaste"] },
  { id: "T319", items: ["Biscuits", "Cheese", "Milk", "Sugar", "Tea"] },
  { id: "T320", items: ["Cooking Oil", "Eggs", "Fish", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T321", items: ["Cheese", "Milk"] },
  { id: "T322", items: ["Biscuits", "Milk", "Sugar", "Tea"] },
  { id: "T323", items: ["Chicken", "Fish", "Milk", "Noodles", "Onion", "Rice", "Spices", "Tomato"] },
  { id: "T324", items: ["Cheese", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices", "Yogurt"] },
  { id: "T325", items: ["Shampoo", "Soap", "Toothpaste"] },
  { id: "T326", items: ["Bananas", "Butter", "Eggs", "Garlic", "Lentils", "Milk"] },
  { id: "T327", items: ["Chips", "Chocolate", "Cooking Oil", "Garlic", "Juice", "Lentils", "Noodles", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T328", items: ["Butter", "Chicken", "Garlic", "Onion", "Potato", "Spices"] },
  { id: "T329", items: ["Cheese", "Lentils", "Milk", "Yogurt"] },
  { id: "T330", items: ["Biscuits", "Lentils", "Milk", "Sugar", "Tea"] },
  { id: "T331", items: ["Bread", "Butter", "Eggs", "Milk", "Sugar"] },
  { id: "T332", items: ["Bananas", "Cooking Oil", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T333", items: ["Cheese", "Lentils", "Yogurt"] },
  { id: "T334", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T335", items: ["Lentils", "Noodles", "Soap", "Toothpaste"] },
  { id: "T336", items: ["Cooking Oil", "Lentils", "Onion", "Salt"] },
  { id: "T337", items: ["Bread", "Chips", "Chocolate", "Noodles"] },
  { id: "T338", items: ["Milk", "Shampoo"] },
  { id: "T339", items: ["Biscuits", "Milk", "Soap", "Sugar", "Tea"] },
  { id: "T340", items: ["Eggs", "Soap", "Sugar", "Tea", "Toothpaste"] },
  { id: "T341", items: ["Cheese", "Fish", "Onion", "Rice", "Spices", "Tomato"] },
  { id: "T342", items: ["Cheese", "Milk", "Yogurt"] },
  { id: "T343", items: ["Biscuits", "Cheese", "Milk", "Sugar", "Tea"] },
  { id: "T344", items: ["Biscuits", "Cheese", "Milk", "Sugar"] },
  { id: "T345", items: ["Eggs", "Potato", "Spices"] },
  { id: "T346", items: ["Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T347", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T348", items: ["Chips", "Chocolate", "Eggs", "Juice", "Noodles", "Soap"] },
  { id: "T349", items: ["Apples", "Cooking Oil", "Garlic", "Lentils", "Onion", "Oranges", "Rice", "Salt", "Spices"] },
  { id: "T350", items: ["Coffee", "Juice", "Soap", "Toothpaste"] },
  { id: "T351", items: ["Garlic", "Lentils", "Noodles", "Onion", "Rice"] },
  { id: "T352", items: ["Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T353", items: ["Eggs", "Lentils", "Milk", "Shampoo", "Soap", "Toothpaste"] },
  { id: "T354", items: ["Cheese", "Cooking Oil", "Garlic", "Onion", "Rice", "Salt", "Soap", "Spices", "Yogurt"] },
  { id: "T355", items: ["Bread", "Butter", "Eggs", "Fish", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T356", items: ["Chips", "Chocolate", "Noodles", "Oranges"] },
  { id: "T357", items: ["Bread", "Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T358", items: ["Biscuits", "Fish", "Milk", "Onion", "Sugar", "Tea"] },
  { id: "T359", items: ["Milk", "Yogurt"] },
  { id: "T360", items: ["Garlic", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T361", items: ["Chicken", "Garlic", "Potato", "Spices", "Tomato"] },
  { id: "T362", items: ["Bread", "Butter", "Eggs", "Juice", "Milk"] },
  { id: "T363", items: ["Eggs", "Milk"] },
  { id: "T364", items: ["Apples", "Bananas", "Flour", "Juice", "Oranges"] },
  { id: "T365", items: ["Apples", "Bananas", "Butter", "Eggs", "Flour", "Juice", "Oranges", "Sugar"] },
  { id: "T366", items: ["Biscuits", "Milk", "Sugar", "Tea"] },
  { id: "T367", items: ["Cheese", "Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T368", items: ["Chicken", "Garlic", "Onion", "Potato", "Spices"] },
  { id: "T369", items: ["Cooking Oil", "Garlic", "Onion", "Salt", "Spices"] },
  { id: "T370", items: ["Bread", "Eggs"] },
  { id: "T371", items: ["Chicken", "Garlic", "Potato", "Spices", "Tomato"] },
  { id: "T372", items: ["Apples", "Bananas", "Juice", "Lentils", "Oranges"] },
  { id: "T373", items: ["Bread", "Butter", "Noodles"] },
  { id: "T374", items: ["Apples", "Bananas", "Juice", "Oranges"] },
  { id: "T375", items: ["Chicken", "Garlic", "Onion", "Spices", "Tomato"] },
  { id: "T376", items: ["Biscuits", "Chicken", "Garlic", "Juice", "Milk", "Onion", "Potato", "Spices", "Sugar", "Tea", "Tomato"] },
  { id: "T377", items: ["Butter", "Fish", "Flour", "Rice", "Sugar", "Tea"] },
  { id: "T378", items: ["Biscuits", "Cheese", "Chips", "Milk", "Sugar", "Tea", "Yogurt"] },
  { id: "T379", items: ["Cooking Oil", "Lentils", "Onion", "Rice", "Salt", "Spices", "Tea"] },
  { id: "T380", items: ["Apples", "Bananas", "Butter", "Cheese", "Cooking Oil", "Eggs", "Juice", "Milk", "Oranges"] },
  { id: "T381", items: ["Chips", "Chocolate", "Juice", "Noodles"] },
  { id: "T382", items: ["Chicken", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T383", items: ["Butter", "Eggs", "Flour", "Garlic", "Onion", "Rice", "Salt", "Shampoo", "Spices", "Sugar", "Tea"] },
  { id: "T384", items: ["Butter", "Eggs", "Flour", "Rice", "Sugar", "Tomato"] },
  { id: "T385", items: ["Chicken", "Potato", "Spices", "Tomato"] },
  { id: "T386", items: ["Bananas", "Bread", "Butter", "Chicken", "Eggs", "Flour", "Garlic", "Onion", "Potato", "Spices"] },
  { id: "T387", items: ["Biscuits", "Butter", "Chicken", "Chocolate", "Milk", "Sugar", "Tea"] },
  { id: "T388", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt"] },
  { id: "T389", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T390", items: ["Bananas", "Bread", "Butter", "Cooking Oil", "Lentils", "Milk", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T391", items: ["Bread", "Butter", "Eggs", "Oranges", "Tea"] },
  { id: "T392", items: ["Chicken", "Garlic", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T393", items: ["Bread", "Fish", "Onion", "Rice", "Spices"] },
  { id: "T394", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices", "Tomato"] },
  { id: "T395", items: ["Bread", "Butter", "Chips", "Chocolate", "Eggs", "Tea"] },
  { id: "T396", items: ["Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T397", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T398", items: ["Chips", "Chocolate", "Juice"] },
  { id: "T399", items: ["Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T400", items: ["Apples", "Bread", "Butter", "Chips", "Eggs", "Milk"] },
  { id: "T401", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt"] },
  { id: "T402", items: ["Butter", "Eggs", "Milk"] },
  { id: "T403", items: ["Bread", "Chips", "Cooking Oil", "Garlic", "Juice", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T404", items: ["Cheese", "Coffee", "Milk", "Yogurt"] },
  { id: "T405", items: ["Biscuits", "Bread", "Butter", "Eggs", "Milk", "Salt", "Sugar"] },
  { id: "T406", items: ["Apples", "Bananas", "Cheese", "Juice", "Oranges"] },
  { id: "T407", items: ["Bread", "Butter", "Cooking Oil", "Eggs", "Lentils", "Milk", "Shampoo"] },
  { id: "T408", items: ["Chips", "Chocolate", "Coffee"] },
  { id: "T409", items: ["Coffee", "Shampoo", "Toothpaste"] },
  { id: "T410", items: ["Biscuits", "Milk", "Sugar", "Tea", "Tomato"] },
  { id: "T411", items: ["Apples", "Bread", "Butter", "Eggs", "Milk"] },
  { id: "T412", items: ["Milk", "Tea"] },
  { id: "T413", items: ["Apples", "Bananas", "Juice", "Oranges"] },
  { id: "T414", items: ["Cooking Oil", "Garlic", "Lentils", "Oranges", "Rice", "Spices", "Yogurt"] },
  { id: "T415", items: ["Bread", "Butter", "Eggs", "Fish", "Milk", "Noodles"] },
  { id: "T416", items: ["Biscuits", "Milk", "Tea", "Tomato"] },
  { id: "T417", items: ["Biscuits", "Coffee", "Milk", "Tea"] },
  { id: "T418", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Potato", "Rice", "Salt", "Spices"] },
  { id: "T419", items: ["Bread", "Butter", "Chicken", "Eggs", "Milk"] },
  { id: "T420", items: ["Biscuits", "Fish", "Milk", "Onion", "Rice", "Sugar", "Tomato"] },
  { id: "T421", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T422", items: ["Bananas", "Coffee", "Juice", "Oranges", "Yogurt"] },
  { id: "T423", items: ["Butter", "Chips", "Chocolate", "Eggs", "Noodles", "Shampoo", "Tea", "Tomato"] },
  { id: "T424", items: ["Chips", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T425", items: ["Apples", "Bananas", "Biscuits", "Chips", "Juice", "Noodles", "Oranges"] },
  { id: "T426", items: ["Cheese", "Milk", "Yogurt"] },
  { id: "T427", items: ["Bananas", "Juice", "Onion"] },
  { id: "T428", items: ["Apples", "Bananas", "Bread", "Butter", "Eggs", "Juice", "Oranges"] },
  { id: "T429", items: ["Fish", "Onion", "Rice", "Salt", "Spices", "Tea", "Tomato"] },
  { id: "T430", items: ["Chicken", "Garlic", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T431", items: ["Garlic", "Lentils", "Onion", "Rice", "Spices", "Tomato"] },
  { id: "T432", items: ["Biscuits", "Chicken", "Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T433", items: ["Biscuits", "Bread", "Butter", "Coffee", "Eggs", "Milk", "Onion"] },
  { id: "T434", items: ["Apples", "Bananas", "Juice", "Tomato"] },
  { id: "T435", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T436", items: ["Cooking Oil", "Lentils", "Onion", "Salt", "Spices"] },
  { id: "T437", items: ["Flour", "Salt"] },
  { id: "T438", items: ["Cooking Oil", "Fish", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T439", items: ["Shampoo", "Soap", "Toothpaste"] },
  { id: "T440", items: ["Soap", "Toothpaste"] },
  { id: "T441", items: ["Bananas", "Butter", "Chocolate", "Cooking Oil", "Eggs", "Fish", "Flour", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Sugar"] },
  { id: "T442", items: ["Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Shampoo", "Spices"] },
  { id: "T443", items: ["Milk", "Oranges", "Sugar", "Tea"] },
  { id: "T444", items: ["Butter", "Cheese", "Eggs", "Flour", "Sugar"] },
  { id: "T445", items: ["Milk", "Sugar", "Tea"] },
  { id: "T446", items: ["Cheese", "Milk", "Yogurt"] },
  { id: "T447", items: ["Bread", "Butter", "Milk", "Spices"] },
  { id: "T448", items: ["Chocolate", "Flour", "Garlic", "Milk", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T449", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T450", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T451", items: ["Lentils", "Oranges", "Shampoo", "Soap"] },
  { id: "T452", items: ["Cooking Oil", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T453", items: ["Butter", "Eggs", "Milk"] },
  { id: "T454", items: ["Bread", "Butter", "Eggs", "Milk"] },
  { id: "T455", items: ["Cooking Oil", "Garlic", "Lentils", "Milk", "Onion", "Rice", "Salt", "Spices", "Toothpaste"] },
  { id: "T456", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T457", items: ["Chicken", "Garlic", "Noodles", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T458", items: ["Biscuits", "Milk", "Sugar", "Tea"] },
  { id: "T459", items: ["Butter", "Eggs", "Flour", "Sugar", "Tea"] },
  { id: "T460", items: ["Bananas", "Bread", "Butter", "Eggs", "Milk", "Rice", "Tea"] },
  { id: "T461", items: ["Biscuits", "Chips", "Garlic", "Lentils", "Onion", "Spices", "Toothpaste"] },
  { id: "T462", items: ["Bananas", "Eggs", "Flour", "Juice", "Spices", "Sugar"] },
  { id: "T463", items: ["Cooking Oil", "Lentils", "Milk", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T464", items: ["Bread", "Butter", "Garlic", "Lentils", "Milk", "Onion", "Oranges", "Rice", "Salt", "Spices"] },
  { id: "T465", items: ["Cheese", "Milk", "Yogurt"] },
  { id: "T466", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices", "Sugar"] },
  { id: "T467", items: ["Chicken", "Garlic", "Onion", "Potato", "Shampoo", "Spices", "Tomato"] },
  { id: "T468", items: ["Apples", "Fish", "Juice", "Onion", "Spices", "Tomato"] },
  { id: "T469", items: ["Bread", "Eggs", "Milk", "Rice", "Spices"] },
  { id: "T470", items: ["Biscuits", "Bread", "Butter", "Eggs", "Fish", "Milk"] },
  { id: "T471", items: ["Fish", "Onion", "Rice", "Spices", "Tomato"] },
  { id: "T472", items: ["Bread", "Butter", "Cooking Oil", "Eggs", "Garlic", "Lentils", "Milk", "Onion", "Rice", "Salt", "Spices", "Tomato"] },
  { id: "T473", items: ["Fish", "Juice", "Onion", "Rice", "Spices", "Tomato"] },
  { id: "T474", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T475", items: ["Biscuits", "Soap", "Tea", "Toothpaste"] },
  { id: "T476", items: ["Bread", "Butter", "Chicken", "Chips", "Chocolate", "Cooking Oil", "Eggs", "Milk", "Noodles", "Salt"] },
  { id: "T477", items: ["Bread", "Butter", "Eggs", "Flour", "Milk", "Potato", "Sugar"] },
  { id: "T478", items: ["Bananas", "Biscuits", "Chips", "Chocolate", "Cooking Oil", "Juice", "Milk", "Noodles", "Sugar", "Tea"] },
  { id: "T479", items: ["Bananas", "Bread", "Butter", "Cheese", "Chicken", "Eggs", "Fish", "Milk"] },
  { id: "T480", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T481", items: ["Bread", "Eggs", "Fish", "Milk", "Onion", "Rice", "Spices", "Tomato"] },
  { id: "T482", items: ["Milk", "Shampoo", "Soap", "Sugar", "Tea", "Tomato", "Toothpaste"] },
  { id: "T483", items: ["Apples", "Bananas", "Juice", "Oranges", "Tomato"] },
  { id: "T484", items: ["Apples", "Bananas", "Butter", "Eggs", "Flour", "Juice", "Sugar"] },
  { id: "T485", items: ["Chocolate", "Coffee", "Garlic", "Juice", "Lentils", "Onion", "Salt", "Shampoo", "Spices"] },
  { id: "T486", items: ["Apples", "Bananas", "Garlic", "Juice", "Lentils", "Oranges", "Rice", "Salt", "Spices"] },
  { id: "T487", items: ["Garlic", "Onion", "Spices"] },
  { id: "T488", items: ["Bread", "Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Toothpaste"] },
  { id: "T489", items: ["Biscuits", "Cheese", "Cooking Oil", "Tea"] },
  { id: "T490", items: ["Cooking Oil", "Garlic", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T491", items: ["Fish", "Lentils", "Onion", "Rice", "Soap", "Spices", "Tomato", "Toothpaste"] },
  { id: "T492", items: ["Bread", "Butter", "Eggs", "Flour", "Milk", "Sugar"] },
  { id: "T493", items: ["Cheese", "Yogurt"] },
  { id: "T494", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt"] },
  { id: "T495", items: ["Eggs", "Flour", "Sugar"] },
  { id: "T496", items: ["Apples", "Bananas", "Chocolate", "Coffee", "Oranges"] },
  { id: "T497", items: ["Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T498", items: ["Shampoo", "Soap", "Toothpaste"] },
  { id: "T499", items: ["Apples", "Bananas", "Juice", "Oranges", "Rice"] },
  { id: "T500", items: ["Chocolate", "Cooking Oil", "Garlic", "Lentils", "Onion", "Rice", "Salt"] },
  { id: "T501", items: ["Biscuits", "Butter", "Fish", "Milk", "Sugar", "Tea"] },
  { id: "T502", items: ["Biscuits", "Bread", "Butter", "Chocolate", "Cooking Oil", "Eggs", "Garlic", "Lentils", "Milk", "Rice", "Salt", "Soap", "Spices"] },
  { id: "T503", items: ["Biscuits", "Cheese", "Milk", "Spices", "Sugar", "Tea", "Yogurt"] },
  { id: "T504", items: ["Chocolate", "Cooking Oil", "Fish", "Garlic", "Lentils", "Noodles", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T505", items: ["Biscuits", "Chocolate", "Juice", "Noodles", "Soap"] },
  { id: "T506", items: ["Bread", "Cooking Oil", "Garlic", "Rice", "Salt", "Spices", "Yogurt"] },
  { id: "T507", items: ["Apples", "Bananas", "Cooking Oil", "Juice", "Lentils", "Rice", "Salt", "Spices"] },
  { id: "T508", items: ["Cooking Oil", "Onion", "Rice", "Spices", "Tomato"] },
  { id: "T509", items: ["Chicken", "Garlic", "Potato", "Shampoo", "Soap", "Spices", "Tomato", "Toothpaste"] },
  { id: "T510", items: ["Bread", "Eggs", "Milk"] },
  { id: "T511", items: ["Bananas", "Flour", "Milk", "Sugar", "Tea"] },
  { id: "T512", items: ["Bread", "Butter", "Eggs", "Flour", "Soap", "Sugar"] },
  { id: "T513", items: ["Apples", "Coffee", "Eggs", "Juice"] },
  { id: "T514", items: ["Cooking Oil", "Lentils", "Onion", "Rice", "Salt", "Spices"] },
  { id: "T515", items: ["Butter", "Chicken", "Garlic", "Onion", "Potato", "Spices", "Tomato"] },
  { id: "T516", items: ["Shampoo", "Soap", "Toothpaste"] },
  { id: "T517", items: ["Chips", "Chocolate", "Juice", "Noodles", "Potato", "Spices", "Tomato"] },
  { id: "T518", items: ["Bread", "Butter", "Eggs", "Milk", "Rice"] },
  { id: "T519", items: ["Butter", "Eggs", "Tomato"] },
  { id: "T520", items: ["Bread", "Butter", "Eggs", "Milk", "Tea"] },
];


/* ==========================================================================
   PART 6 : START BUTTON
   Decides where we are running: in the terminal (Node.js) or the browser.
   ========================================================================== */

if (typeof document !== "undefined") {
  // We are in a BROWSER -> build the web page once it has loaded.
  document.addEventListener("DOMContentLoaded", setupBrowserPage);
} else {
  // We are in the TERMINAL (Node.js).
  // "process.argv[2]" is whatever you typed after "node script.js".
  const typedValue = process.argv[2];
  const minSupport = typedValue === undefined ? DEFAULT_MIN_SUPPORT : Number(typedValue);

  if (!Number.isInteger(minSupport) || minSupport < 1 || minSupport > transactions.length) {
    console.log("Please give a whole number from 1 to " + transactions.length + ".");
    console.log("Example:  node script.js 50");
  } else {
    const result = runApriori(transactions, minSupport);
    printToTerminal(result);
  }
}
