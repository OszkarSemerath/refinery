package tools.refinery.store.partial.rule;

import tools.refinery.store.partial.PartialInterpretation;
import tools.refinery.store.partial.representation.PartialRelation;
import tools.refinery.store.model.Model;
import tools.refinery.store.query.Variable;
import tools.refinery.store.representation.TruthValue;
import tools.refinery.store.tuple.Tuple;

import java.util.List;

public record RelationRefinementAction(PartialRelation target, List<Variable> arguments, TruthValue value)
		implements RuleAction {
	public RelationRefinementAction {
		if (arguments.size() != target.arity()) {
			throw new IllegalArgumentException("%s needs %d parameters, but got %s".formatted(target.name(),
					target.arity(), arguments.size()));
		}
		if (value == TruthValue.UNKNOWN) {
			throw new IllegalArgumentException("Refining with UNKNOWN has no effect");
		}
	}

	@Override
	public RuleActionExecutor createExecutor(int[] argumentIndices, Model model) {
		var targetInterpretation = model.getAdapter(PartialInterpretation.ADAPTER).getPartialInterpretation(target);
		return activationTuple -> {
			int arity = argumentIndices.length;
			var arguments = new int[arity];
			for (int i = 0; i < arity; i++) {
				arguments[i] = activationTuple.get(argumentIndices[i]);
			}
			return targetInterpretation.merge(Tuple.of(arguments), value);
		};
	}
}
