/*******************************************************************************
* SAT4J: a SATisfiability library for Java Copyright (C) 2004-2008 Daniel Le Berre
*
* All rights reserved. This program and the accompanying materials
* are made available under the terms of the Eclipse Public License v1.0
* which accompanies this distribution, and is available at
* http://www.eclipse.org/legal/epl-v10.html
*
* Alternatively, the contents of this file may be used under the terms of
* either the GNU Lesser General Public License Version 2.1 or later (the
* "LGPL"), in which case the provisions of the LGPL are applicable instead
* of those above. If you wish to allow use of your version of this file only
* under the terms of the LGPL, and not to allow others to use your version of
* this file under the terms of the EPL, indicate your decision by deleting
* the provisions above and replace them with the notice and other provisions
* required by the LGPL. If you do not delete the provisions above, a recipient
* may use your version of this file under the terms of the EPL or the LGPL.
* 
* Based on the original MiniSat specification from:
* 
* An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
* Sixth International Conference on Theory and Applications of Satisfiability
* Testing, LNCS 2919, pp 502-518, 2003.
*
* See www.minisat.se for the original solver in C++.
* 
*******************************************************************************/
package org.sat4j.tools;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * Class dedicated to Remi Coletta utility methods :-)
 * 
 * @author leberre
 */
public class RemiUtils {

    private RemiUtils() {
        // no instanceof that class are expected to be used.
    }

    /**
     * Compute the set of literals common to all models of the formula.
     * 
     * @param s
     *            a solver already feeded
     * @return the set of literals common to all models of the formula contained
     *         in the solver, in dimacs format.
     * @throws TimeoutException
     */
    public static IVecInt backbone(ISolver s) throws TimeoutException {
        IVecInt backbone = new VecInt();
        int nvars = s.nVars();
        for (int i = 1; i <= nvars; i++) {
            backbone.push(i);
            if (s.isSatisfiable(backbone)) {
                backbone.pop().push(-i);
                if (s.isSatisfiable(backbone)) {
                    backbone.pop();
                } else {
                    // -i is in the backbone
                    backbone.pop().push(i);
                }
            } else {
                // -i is in the backbone
                backbone.pop().push(-i);
            }
        }
        return backbone;
    }

}