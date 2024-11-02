/*
 * SPDX-FileCopyrightText: 2023-2024 The Refinery Authors <https://refinery.tools/>
 *
 * SPDX-License-Identifier: EPL-2.0
 */
package tools.refinery.store.reasoning.translator.crossreference;

import tools.refinery.store.reasoning.representation.PartialRelation;
import tools.refinery.store.reasoning.translator.multiplicity.Multiplicity;
import tools.refinery.logic.term.truthvalue.TruthValue;

import java.util.LinkedHashSet;
import java.util.Set;

public record UndirectedCrossReferenceInfo(PartialRelation type, Multiplicity multiplicity, TruthValue defaultValue,
										   boolean partial, Set<PartialRelation> supersets) {
	public boolean isConstrained() {
		return multiplicity.isConstrained();
	}
}
