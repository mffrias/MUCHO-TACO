/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4compiler.translator;

import java.io.Serializable;
import java.util.prefs.Preferences;
import edu.mit.csail.sdg.alloy4.ErrorAPI;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.Util;

/** Mutable; this class encapsulates the customizable options of the Alloy-to-Kodkod translator. */

public final class A4Options implements Serializable {

    /** This enum defines the set of possible SAT solvers. */
    public static final class SatSolver implements Serializable {
        /** This ensures the class can be serialized reliably. */
        private static final long serialVersionUID = 0;
        /** List of all existing SatSolver values. */
        private static final SafeList<SatSolver> values = new SafeList<SatSolver>();
        /** This is a unique String for this value; it should be kept consistent in future versions. */
        private final String id;
        /** This is the label that the toString() method will return. */
        private final String toString;
        /** If not null, this is the external command-line solver to use. */
        private final String external;
        /** If not null, this is the set of options to use with the command-line solver. */
        private final String[] options;
        /** Constructs a new SatSolver value. */
        private SatSolver(String id, String toString, String external, String[] options, boolean add) {
            this.id=id;
            this.toString=toString;
            this.external=external;
            this.options=new String[options!=null ? options.length : 0];
            for(int i=0; i<this.options.length; i++) this.options[i] = options[i];
            if (add) { synchronized(SatSolver.class) { values.add(this); } }
        }
        /** Constructs a new SatSolver value that uses a command-line solver; throws ErrorAPI if the ID is already in use. */
        public static SatSolver make(String id, String toString, String external, String[] options) throws ErrorAPI {
            if (id==null || toString==null || external==null) throw new ErrorAPI("NullPointerException in SatSolver.make()");
            SatSolver ans = new SatSolver(id, toString, external, options, false);
            synchronized(SatSolver.class) {
               for(SatSolver x: values)
                  if (x.id.equals(id))
                     throw new ErrorAPI("The SatSolver id \""+id+"\" is already in use.");
               values.add(ans);
            }
            return ans;
        }
        /** Constructs a new SatSolver value that uses a command-line solver; throws ErrorAPI if the ID is already in use. */
        public static SatSolver make(String id, String toString, String external) throws ErrorAPI { return make(id, toString, external, null); }
        /** Returns the executable for the external command-line solver to use (or null if this solver does not use an external commandline solver) */
        public String external() { return external; }
        /** Returns the options for the external command-line solver to use (or empty array if this solver does not use an external commandline solver) */
        public String[] options() {
            if (external==null || options.length==0) return new String[0];
            String[] ans = new String[options.length];
            for(int i=0; i<ans.length; i++) ans[i] = options[i];
            return ans;
        }
        /** Returns the unique String for this value; it will be kept consistent in future versions. */
        public String id() { return id; }
        /** Returns the list of SatSolver values. */
        public static SafeList<SatSolver> values() {
            SafeList<SatSolver> ans;
            synchronized(SatSolver.class) { ans=values.dup(); }
            return ans;
        }
        /** Returns the human-readable label for this enum value. */
        @Override public String toString() { return toString; }
        /** Ensures we can use == to do comparison. */
        private Object readResolve() {
            synchronized(SatSolver.class) {
                for(SatSolver x:values) if (x.id.equals(id)) return x;
                values.add(this);
            }
            return this;
        }
        /** Given an id, return the enum value corresponding to it (if there's no match, then return SAT4J). */
        public static SatSolver parse(String id) {
            synchronized(SatSolver.class) { for(SatSolver x:values) if (x.id.equals(id)) return x; }
            return SAT4J;
        }
        /** Saves this value into the Java preference object. */
        public void set() { Preferences.userNodeForPackage(Util.class).put("SatSolver2",id); }
        /** Reads the current value of the Java preference object (if it's not set, then return SAT4J). */
        public static SatSolver get() { return parse(Preferences.userNodeForPackage(Util.class).get("SatSolver2","")); }
        /** BerkMin via pipe */
        public static final SatSolver BerkMinPIPE = new SatSolver("berkmin", "BerkMin", "berkmin", null, true);
        /** Spear via pipe */
        public static final SatSolver SpearPIPE = new SatSolver("spear", "Spear", "spear", new String[]{"--model", "--dimacs"}, true);
        /** MiniSat1 via JNI */
        public static final SatSolver MiniSatJNI = new SatSolver("minisat(jni)", "Minisat", null, null, true);
        /** MiniSat220 via JNI, added by RFM */
        public static final SatSolver MiniSat220JNI = new SatSolver("minisat220(jni)", "Minisat v220", null, null, true);
        /** MiniSat220Simp via JNI, added by RFM */
        public static final SatSolver MiniSat220SimpJNI = new SatSolver("minisat220simp(jni)", "Minisat v220_simp", null, null, true);
        /** Lingeling via JNI, added by RFM */
        public static final SatSolver LingelingJNI = new SatSolver("lingeling(jni)", "Lingeling v276", null, null, true);
        /** MiniSatProver1 via JNI */
        public static final SatSolver MiniSatProverJNI = new SatSolver("minisatprover(jni)", "MinisatProver_UC", null, null, true);
        /** ZChaff via JNI */
        public static final SatSolver ZChaffJNI = new SatSolver("zchaff(jni)", "ZChaff", null, null, true);
        /** SAT4J using native Java */
        public static final SatSolver SAT4J = new SatSolver("sat4j", "SAT4J", null, null, true);
        /** Outputs the raw CNF file only (to a tempfile) */
        public static final SatSolver CNF = new SatSolver("cnf", "Output CNF to file", null, null, true);
        /** Outputs the raw CNF file only (to standard output) */
        public static final SatSolver CNFSTDOUT = new SatSolver("cnfstdout", "Output CNF to stdout", null, null, true);
        /** Outputs the raw Kodkod file only */
        public static final SatSolver KK = new SatSolver("kodkod", "Output Kodkod to file", null, null, true);
    }

    /** This ensures the class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /** Constructs an A4Options object with default values for everything. */
    public A4Options() { }

    /** This option specifies the amount of symmetry breaking to do (when symmetry breaking isn't explicitly disabled).
     *
     * <p> If a formula is unsatisfiable, then in general, the higher this value,
     * the faster you finish the solving. But if this value is too high, it will instead slow down the solving.
     *
     * <p> If a formula is satisfiable, then in general, the lower this value, the faster you finish the solving.
     * Setting this value to 0 usually gives the fastest solve.
     *
     * <p> Default value is 20.
     */
    public int symmetry = 20;

    /** This option specifies the maximum skolem-function depth.
     * <p> Default value is 0, which means it will only generate skolem constants, and will not generate skolem functions.
     */
    public int skolemDepth = 0;

    /** This option specifies the unsat core minimization strategy (0=GuaranteedLocalMinimum 1=FasterButLessAccurate 2=EvenFaster...)
     * <p> Default value is set to the fastest current strategy.
     */
    public int coreMinimization = 2;

    /** This option specifies the SAT solver to use (SAT4J, MiniSatJNI, MiniSatProverJNI, ZChaffJNI...)
     * <p> Default value is SAT4J.
     */
    public SatSolver solver = SatSolver.SAT4J;

    /** When this.solver is external, and the solver filename is a relative filename, then this option specifies
     * the directory that the solver filename is relative to.
     */
    public String solverDirectory = "";

    /** This specifies the directory where we may write temporary files to. */
    public String tempDirectory = System.getProperty("java.io.tmpdir");

    /** This option tells the compiler the "original filename" that these AST nodes came from;
     * it is only used for generating comments and other diagnostic messages.
     * <p> Default value is "".
     */
    public String originalFilename = "";

    /** This option specifies whether the compiler should record
     * the original Kodkod formula being generated and the resulting Kodkod instances.
     * <p> Default value is false.
     */
    public boolean recordKodkod = false;

    /** This option constrols how deep we unroll loops and unroll recursive predicate/function/macros (negative means it's disallowed) */
    public int unrolls = (-1);

    /** This method makes a copy of this Options object. */
    public A4Options dup() {
        A4Options x = new A4Options();
        x.unrolls = unrolls;
        x.symmetry = symmetry;
        x.skolemDepth = skolemDepth;
        x.coreMinimization = coreMinimization;
        x.solver = solver;
        x.solverDirectory = solverDirectory;
        x.tempDirectory = tempDirectory;
        x.originalFilename = originalFilename;
        x.recordKodkod = recordKodkod;
        return x;
    }
}
