/*
 * SPDX-FileCopyrightText: 2021-2024 The Refinery Authors <https://refinery.tools/>
 *
 * SPDX-License-Identifier: EPL-2.0
 */
package tools.refinery.store.reasoning.internal;

import tools.refinery.store.dse.propagation.PropagationAdapter;
import tools.refinery.store.dse.propagation.PropagationResult;
import tools.refinery.store.model.Model;
import tools.refinery.store.model.ModelStore;
import tools.refinery.store.query.ModelQueryAdapter;
import tools.refinery.store.reasoning.ReasoningAdapter;
import tools.refinery.store.reasoning.ReasoningStoreAdapter;
import tools.refinery.store.reasoning.interpretation.PartialInterpretation;
import tools.refinery.store.reasoning.literal.Concreteness;
import tools.refinery.store.reasoning.refinement.PartialInterpretationRefiner;
import tools.refinery.store.reasoning.refinement.PartialModelInitializer;
import tools.refinery.store.reasoning.refinement.StorageRefiner;
import tools.refinery.store.reasoning.representation.AnyPartialSymbol;
import tools.refinery.store.reasoning.seed.ModelSeed;
import tools.refinery.store.reasoning.seed.PropagatedModel;
import tools.refinery.store.representation.AnySymbol;
import tools.refinery.store.representation.Symbol;
import tools.refinery.store.tuple.Tuple;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

class ReasoningStoreAdapterImpl implements ReasoningStoreAdapter {
	private final ModelStore store;
	private final Set<Concreteness> supportedInterpretations;
	private final Map<AnyPartialSymbol, PartialInterpretation.Factory<?, ?>> symbolInterpreters;
	private final Map<AnyPartialSymbol, PartialInterpretationRefiner.Factory<?, ?>> symbolRefiners;
	private final Map<AnySymbol, StorageRefiner.Factory<?>> storageRefiners;
	private final List<PartialModelInitializer> initializers;

	ReasoningStoreAdapterImpl(ModelStore store, Set<Concreteness> supportedInterpretations,
							  Map<AnyPartialSymbol, PartialInterpretation.Factory<?, ?>> symbolInterpreters,
							  Map<AnyPartialSymbol, PartialInterpretationRefiner.Factory<?, ?>> symbolRefiners,
							  Map<AnySymbol, StorageRefiner.Factory<?>> storageRefiners,
							  List<PartialModelInitializer> initializers) {
		this.store = store;
		this.supportedInterpretations = supportedInterpretations;
		this.symbolInterpreters = symbolInterpreters;
		this.symbolRefiners = symbolRefiners;
		this.storageRefiners = storageRefiners;
		this.initializers = initializers;
	}

	@Override
	public ModelStore getStore() {
		return store;
	}

	@Override
	public Set<Concreteness> getSupportedInterpretations() {
		return supportedInterpretations;
	}

	@Override
	public Collection<AnyPartialSymbol> getPartialSymbols() {
		return symbolInterpreters.keySet();
	}

	@Override
	public Collection<AnyPartialSymbol> getRefinablePartialSymbols() {
		return symbolRefiners.keySet();
	}

	// Use of wildcard return value only in internal method not exposed as API, so there is less chance of confusion.
	@SuppressWarnings("squid:S1452")
	Map<AnyPartialSymbol, PartialInterpretation.Factory<?, ?>> getSymbolInterpreters() {
		return symbolInterpreters;
	}

	// Use of wildcard return value only in internal method not exposed as API, so there is less chance of confusion.
	@SuppressWarnings("squid:S1452")
	Map<AnyPartialSymbol, PartialInterpretationRefiner.Factory<?, ?>> getSymbolRefiners() {
		return symbolRefiners;
	}

	StorageRefiner[] createStorageRefiner(Model model) {
		var refiners = new StorageRefiner[storageRefiners.size()];
		int i = 0;
		for (var entry : storageRefiners.entrySet()) {
			var symbol = entry.getKey();
			var factory = entry.getValue();
			refiners[i] = createStorageRefiner(factory, model, symbol);
			i++;
		}
		return refiners;
	}

	private <T> StorageRefiner createStorageRefiner(StorageRefiner.Factory<T> factory, Model model, AnySymbol symbol) {
		// The builder only allows well-typed assignment of refiners to symbols.
		@SuppressWarnings("unchecked")
		var typedSymbol = (Symbol<T>) symbol;
		return factory.create(typedSymbol, model);
	}

	@Override
	public PropagatedModel tryCreateInitialModel(ModelSeed modelSeed) {
		var model = store.createEmptyModel();
		return tryResetInitialModel(model,modelSeed);
	}

	public PropagatedModel tryResetInitialModel(Model model, ModelSeed modelSeed) {
		try {
			model.getInterpretation(ReasoningAdapterImpl.NODE_COUNT_SYMBOL).put(Tuple.of(), modelSeed.getNodeCount());
			for (var initializer : initializers) {
				initializer.initialize(model, modelSeed);
			}
			var reasoningAdapter = ((ReasoningAdapterImpl) model.getAdapter(ReasoningAdapter.class));
			reasoningAdapter.afterInitialize(modelSeed);
			var propagationResult = model.tryGetAdapter(PropagationAdapter.class)
					.map(PropagationAdapter::propagate)
					.orElse(PropagationResult.UNCHANGED);
			model.getAdapter(ModelQueryAdapter.class).flushChanges();
			return new PropagatedModel(model, propagationResult);
		} catch (RuntimeException e) {
			model.close();
			throw e;
		}
	}

	@Override
	public ReasoningAdapterImpl createModelAdapter(Model model) {
		return new ReasoningAdapterImpl(model, this);
	}
}
