/*********************************************************************[microsat.c]***

  The MIT License

  Copyright (c) 2014-2018 Marijn Heule

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.

*************************************************************************************/
#include <stdio.h>
#include <stdlib.h>

struct micro_solver {
    enum {
        END = -9, UNSAT = 0, SAT = 1, MARK = 2, IMPLIED = 6
    };

public:
    int *DB;
    int nVars;
    int nClauses;
    int mem_used;
    int mem_fixed;
    int mem_max;
    int maxLemmas;
    int nLemmas;
    int *buffer;
    int nConflicts;
    // TODO: set maxconflicts for "timeout"
    int maxconflicts = INT_MAX;
    int *model;
    int *reason;
    int *mfalseStack;
    int *mfalse;
    int *first;
    int *forced;
    int *processed;
    int *assigned;
    int *next;
    int *prev;
    int head;
    int res;
    int fast;
    int slow;

public:
    micro_solver() {
    }
    ;

    ~micro_solver() {
        // TODO: is this right?
        if (DB) {
            free(DB);
        }
    }


    void unassign(int lit) {
        this->mfalse[lit] = 0;                                       // Unassign the literal
    }

    void restart() {                                                 // Perform a restart (i.e., unassign all variables)
        while (this->assigned > this->forced)
            unassign(*(--this->assigned));                           // Remove all unforced false lits from falseStack
        this->processed = this->forced;                              // Reset the processed pointer
    }

    void assign(int* reason, int forced) {                           // Make the first literal of the reason true
        int lit = reason[0];                                         // Let lit be the first ltieral in the reason
        this->mfalse[-lit] = forced ? IMPLIED : 1;                   // Mark lit as true and IMPLIED if forced
        *(this->assigned++) = -lit;                                  // Push it on the assignment stack
        this->reason[abs(lit)] = 1 + (int) ((reason) - this->DB);    // Set the reason clause of lit
        this->model[abs(lit)] = (lit > 0);                           // Mark the literal as true in the model
    }

    void addWatch(int lit, int mem) {                                // Add a watch pointer to a clause containing lit
        this->DB[mem] = this->first[lit];                            // By updating the database and the pointers
        this->first[lit] = mem;
    }

    int* getMemory(int mem_size) {                       // Allocate memory of size mem_size
        if (this->mem_used + mem_size > this->mem_max) { // In case the code is used within a code base
            printf("c out of memory\n");
            exit(0);
        }
        int *store = (this->DB + this->mem_used);         // Compute a pointer to the new memory location
        this->mem_used += mem_size;                       // Update the size of the used memory
        return store;                                     // Return the pointer
    }

    int* addClause(int* in, int size, int irr) {          // Adds a clause stored in *in of size size
        int i, used = this->mem_used;                     // Store a pointer to the beginning of the clause
        int* clause = getMemory(size + 3) + 2;            // Allocate memory for the clause in the database
        if (size > 1) {
            addWatch(in[0], used);                        // If the clause is not unit, then add
            addWatch(in[1], used + 1);                    // Two watch pointers to the datastructure
        }
        for (i = 0; i < size; i++)
            clause[i] = in[i];                            // Copy the clause from the buffer to the database
        clause[i] = 0;
        if (irr)
            this->mem_fixed = this->mem_used;
        else
            this->nLemmas++;                             // Update the statistics
        return clause;                                   // Return the pointer to the clause is the database
    }

    void reduceDB(int k) { // Removes "less useful" lemmas from DB
        while (this->nLemmas > this->maxLemmas)
            this->maxLemmas += 300;                     // Allow more lemmas in the future
        this->nLemmas = 0;                              // Reset the number of lemmas

        int i;
        for (i = -this->nVars; i <= this->nVars; i++) {  // Loop over the variables
            if (i == 0)
                continue;
            int* watch = &this->first[i];               // Get the pointer to the first watched clause
            while (*watch != END)                       // As long as there are watched clauses
                if (*watch < this->mem_fixed)
                    watch = (this->DB + *watch);        // Remove the watch if it points to a lemma
                else
                    *watch = this->DB[*watch];          // Otherwise (meaning an input clause) go to next watch
        }

        int old_used = this->mem_used;
        this->mem_used = this->mem_fixed;                      // Virtually remove all lemmas
        for (i = this->mem_fixed + 2; i < old_used; i += 3) {  // While the old memory contains lemmas
            int count = 0, head = i;                           // Get the lemma to which the head is pointing
            while (this->DB[i]) {
                int lit = this->DB[i++];                       // Count the number of literals
                if ((lit > 0) == this->model[abs(lit)])        // That are satisfied by the current model
                    count++;
            }
            if (count < k)
                addClause(this->DB + head, i - head, 0);       // If the latter is smaller than k, add it back
        }
    }

    void bump(int lit) {                                       // Move the variable to the front of the decision list
        if (this->mfalse[lit] != IMPLIED) {
            this->mfalse[lit] = MARK;                          // MARK the literal as involved if not a top-level unit
            int var = abs(lit);
            if (var != this->head) {                           // In case var is not already the head of the list
                this->prev[this->next[var]] = this->prev[var]; // Update the prev link, and
                this->next[this->prev[var]] = this->next[var]; // Update the next link, and
                this->next[this->head] = var;                  // Add a next link to the head, and
                this->prev[var] = this->head;                  // Make var the new head
                this->head = var;
            }
        }
    }

    int implied(int lit) {                                    // Check if lit(eral) is implied by MARK literals
        if (this->mfalse[lit] > MARK)
            return (this->mfalse[lit] & MARK);                // If checked before return old result
        if (!this->reason[abs(lit)])
            return 0;                                         // In case lit is a decision, it is not implied
        int* p = (this->DB + this->reason[abs(lit)] - 1);     // Get the reason of lit(eral)
        while (*(++p))                                        // While there are literals in the reason
            if ((this->mfalse[*p] ^ MARK) && !implied(*p)) {  // Recursively check if non-MARK literals are implied
                this->mfalse[lit] = IMPLIED - 1;              // Mark and return not implied (denoted by IMPLIED - 1)
                return 0;                                     // Mark and return that the literal is implied
            }
        this->mfalse[lit] = IMPLIED;
        return 1;
    }

    int* analyze(int* clause) {                               // Compute a resolvent from falsified clause
        this->res++;
        this->nConflicts++;                                   // Bump restarts and update the statistic
        while (*clause)
            bump(*(clause++));                                // MARK all literals in the falsified clause
        while (this->reason[abs(*(--this->assigned))]) {      // Loop on variables on falseStack until the last decision
            if (this->mfalse[*this->assigned] == MARK) {      // If the tail of the stack is MARK
                int *check = this->assigned;                  // Pointer to check if first-UIP is reached
                while (this->mfalse[*(--check)] != MARK)      // Check for a MARK literal before decision
                    if (!this->reason[abs(*check)])
                        goto build;
                // Otherwise it is the first-UIP so break
                clause = this->DB + this->reason[abs(*this->assigned)]; // Get the reason and ignore first literal
                while (*clause)                                // MARK all literals in reason
                    bump(*(clause++));
            }
            unassign(*this->assigned);                         // Unassign the tail of the stack
        }

        build: ;
        int size = 0, lbd = 0, flag = 0;                      // Build conflict clause; Empty the clause buffer
        int* p = this->processed = this->assigned;            // Loop from tail to front
        while (p >= this->forced) {                           // Only literals on the stack can be MARKed
            if ((this->mfalse[*p] == MARK) && !implied(*p)) { // If MARKed and not implied
                this->buffer[size++] = *p;
                flag = 1;
            }                                                 // Add literal to conflict clause buffer
            if (!this->reason[abs(*p)]) {
                lbd += flag;
                flag = 0;                                     // Increase LBD for a decision with a true flag
                if (size == 1)
                    this->processed = p;
            }                                                 // And update the processed pointer
            this->mfalse[*(p--)] = 1;                         // Reset the MARK flag for all variables on the stack
        }

        this->fast -= this->fast >> 5;
        this->fast += lbd << 15;                              // Update the fast moving average
        this->slow -= this->slow >> 15;
        this->slow += lbd << 5;                               // Update the slow moving average

        while (this->assigned > this->processed)              // Loop over all unprocessed literals
            unassign(*(this->assigned--));                    // Unassign all lits between tail & head
        unassign(*this->assigned);                            // Assigned now equal to processed
        this->buffer[size] = 0;                               // Terminate the buffer (and potentially print clause)
        return addClause(this->buffer, size, 0);              // Add new conflict clause to redundant DB
    }

    int propagate() {                                         // Performs unit propagation
        int forced = this->reason[abs(*this->processed)];     // Initialize forced flag
        while (this->processed < this->assigned) {            // While unprocessed false literals
            int lit = *(this->processed++);                   // Get first unprocessed literal
            int* watch = &this->first[lit];                   // Obtain the first watch pointer
            while (*watch != END) {                           // While there are watched clauses (watched by lit)
                int i, unit = 1;                              // Let's assume that the clause is unit
                int* clause = (this->DB + *watch + 1);        // Get the clause from DB
                if (clause[-2] == 0)
                    clause++;                                 // Set the pointer to the first literal in the clause
                if (clause[0] == lit)
                    clause[0] = clause[1];                    // Ensure that the other watched literal is in front
                for (i = 2; unit && clause[i]; i++)           // Scan the non-watched literals
                    if (!this->mfalse[clause[i]]) {           // When clause[i] is not false, it is either true or unset
                        clause[1] = clause[i];
                        clause[i] = lit;                      // Swap literals
                        int store = *watch;
                        unit = 0;                             // Store the old watch
                        *watch = this->DB[*watch];            // Remove the watch from the list of lit
                        addWatch(clause[1], store);           // Add the watch to the list of clause[1]
                    }
                if (unit) {                                   // If the clause is indeed unit
                    clause[1] = lit;
                    watch = (this->DB + *watch);              // Place lit at clause[1] and update next watch
                    if (this->mfalse[-clause[0]])
                        continue;                             // If the other watched literal is satisfied continue
                    if (!this->mfalse[clause[0]]) {           // If the other watched literal is falsified,
                        assign(clause, forced);               // A unit clause is found, and the reason is set
                    }
                    else {
                        if (forced)
                            return UNSAT;                     // Found a root level conflict -> UNSAT
                        int* lemma = analyze(clause);         // Analyze the conflict return a conflict clause
                        if (!lemma[1])
                            forced = 1;                       // In case a unit clause is found, set forced flag
                        assign(lemma, forced);                // Assign the conflict clause as a unit
                        break;
                    }
                }
            }
        }
        if (forced)
            this->forced = this->processed;                       // Set this->forced if applicable
        return SAT;                                               // Finally, no conflict was found
    }

    int solve() {                                                 // Determine satisfiability
        int decision = this->head;
        this->res = 0;                                            // Initialize the micro_solver
        for (;;) {                                                // Main solve loop
            int old_nLemmas = this->nLemmas;                      // Store nLemmas to see whether propagate adds lemmas
            if (propagate() == UNSAT)
                return UNSAT;                                     // Propagation returns UNSAT for a root level conflict

            if (this->nLemmas > old_nLemmas) {                    // If the last decision caused a conflict
                decision = this->head;                            // Reset the decision heuristic to head
                if (this->fast > (this->slow / 100) * 60) {      // If fast average is substantially larger than slow average
                // printf("c restarting after %i conflicts (%i %i) %i\n", this->res, this->fast, this->slow, this->nLemmas > this->maxLemmas);
                    this->res = 0;
                    this->fast = (this->slow / 100) * 60;
                    restart();                                    // Restart and update the averages
                    if (this->nLemmas > this->maxLemmas)
                        reduceDB(6);                              // Reduce the DB when it contains too many lemmas
                }
            }

            while (this->mfalse[decision] || this->mfalse[-decision]) { // As long as the temporay decision is assigned
                decision = this->prev[decision];                     // Replace it with the next variable in the decision list
            }
            if (decision == 0)
                return SAT;                                          // If the end of the list is reached, then a solution is found
            decision = this->model[decision] ? decision : -decision; // Otherwise, assign the decision variable based on the model
            this->mfalse[-decision] = 1;                             // Assign the decision literal to true (change to IMPLIED-1?)
            *(this->assigned++) = -decision;                         // And push it on the assigned stack
            decision = abs(decision);
            this->reason[decision] = 0;                              // Decisions have no reason clauses
        }
    }

    void initCDCL(int n, int m) {
        if (n < 1)
            n = 1;                                        // The code assumes that there is at least one variable
        this->nVars = n;                                  // Set the number of variables
        this->nClauses = m;                               // Set the number of clauases
        this->mem_max = 1 << 30;                          // Set the initial maximum memory
        this->mem_used = 0;                               // The number of integers allocated in the DB
        this->nLemmas = 0;                                // The number of learned clauses -- redundant means learned
        this->nConflicts = 0;                             // Under of conflicts which is used to updates scores
        this->maxLemmas = 3000;                           // Initial maximum number of learnt clauses
        this->fast = this->slow = 1 << 24;                // Initialize the fast and slow moving averages

        this->DB = (int *) malloc(sizeof(int) * this->mem_max); // Allocate the initial database
        this->model = getMemory(n + 1);                   // Full assignment of the (Boolean) variables (initially set to false)
        this->next = getMemory(n + 1);                    // Next variable in the heuristic order
        this->prev = getMemory(n + 1);                    // Previous variable in the heuristic order
        this->buffer = getMemory(n);                      // A buffer to store a temporary clause
        this->reason = getMemory(n + 1);                  // Array of clauses
        this->mfalseStack = getMemory(n + 1);             // Stack of falsified literals -- this pointer is never changed
        this->forced = this->mfalseStack;                 // Points inside *falseStack at first decision (unforced literal)
        this->processed = this->mfalseStack;              // Points inside *falseStack at first unprocessed literal
        this->assigned = this->mfalseStack;               // Points inside *falseStack at last unprocessed literal
        this->mfalse = getMemory(2 * n + 1);
        this->mfalse += n;                                // Labels for variables, non-zero means false
        this->first = getMemory(2 * n + 1);
        this->first += n;                                 // Offset of the first watched clause
        this->DB[this->mem_used++] = 0;                   // Make sure there is a 0 before the clauses are loaded.

        int i;
        for (i = 1; i <= n; i++) {                        // Initialize the main datastructes:
            this->prev[i] = i - 1;
            this->next[i - 1] = i;                        // the double-linked list for variable-move-to-front,
            this->model[i] = this->mfalse[-i] = this->mfalse[i] = 0; // the model (phase-saving), the false array,
            this->first[i] = this->first[-i] = END;       // and first (watch pointers).
        }
        this->head = n;                                   // Initialize the head of the double-linked list
    }

    // Not used.
    int parse(char* filename) {                                         // Parse the formula and initialize
        int tmp;
        FILE* input = fopen(filename, "r");
        do {
            tmp = fscanf(input, " p cnf %i %i \n", &this->nVars, &this->nClauses);
            if (tmp > 0 && tmp != EOF)
                break;
            tmp = fscanf(input, "%*s\n");
        }                                                               // In case a commment line was found
        while (tmp != 2 && tmp != EOF);                                 // Skip it and read next line

        initCDCL(this->nVars, this->nClauses);                          // Allocate the main datastructures
        int nZeros = this->nClauses, size = 0;                          // Initialize the number of clauses to read
        while (nZeros > 0) {                                            // While there are clauses in the file
            int lit = 0;
            tmp = fscanf(input, " %i ", &lit);                          // Read a literal.
            if (!lit) {                                                 // If reaching the end of the clause
                int* clause = addClause(this->buffer, size, 1);         // Then add the clause to data_base
                if (!size || ((size == 1) && this->mfalse[clause[0]]))  // Check for empty clause or conflicting unit
                    return UNSAT;                                       // If either is found return UNSAT
                if ((size == 1) && !this->mfalse[-clause[0]]) {         // Check for a new unit
                    assign(clause, 1);                                  // Directly assign new units (forced = 1)
                }
                size = 0;
                --nZeros;
            }
            else
                this->buffer[size++] = lit;                             // Add literal to buffer
        }
        fclose(input);
        return SAT;                                                     // Return that no conflict was observed
    }
};
