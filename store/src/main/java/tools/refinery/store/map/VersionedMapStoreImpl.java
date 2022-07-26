package tools.refinery.store.map;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.collections.api.set.primitive.MutableLongSet;
import org.eclipse.collections.impl.map.mutable.primitive.LongObjectHashMap;

import tools.refinery.store.map.internal.ImmutableNode;
import tools.refinery.store.map.internal.MapDiffCursor;
import tools.refinery.store.map.internal.Node;
import tools.refinery.store.map.internal.VersionedMapImpl;

public class VersionedMapStoreImpl<K, V> implements VersionedMapStore<K, V> {
	// Configuration
	private final boolean immutableWhenCommiting;

	// Static data
	protected final ContinousHashProvider<K> hashProvider;
	protected final V defaultValue;

	// Dynamic data
	protected final LongObjectHashMap<ImmutableNode<K, V>> states = new LongObjectHashMap<>();
	protected final Map<Node<K, V>, ImmutableNode<K, V>> nodeCache;
	protected long nextID = 0;

	public VersionedMapStoreImpl(ContinousHashProvider<K> hashProvider, V defaultValue,
			VersionedMapStoreConfiguration config) {
		this.immutableWhenCommiting = config.isImmutableWhenCommiting();
		this.hashProvider = hashProvider;
		this.defaultValue = defaultValue;
		if (config.isSharedNodeCacheInStore()) {
			nodeCache = createNodeCache();
		} else {
			nodeCache = null;
		}
	}

	private VersionedMapStoreImpl(ContinousHashProvider<K> hashProvider, V defaultValue,
			Map<Node<K, V>, ImmutableNode<K, V>> nodeCache, VersionedMapStoreConfiguration config) {
		this.immutableWhenCommiting = config.isImmutableWhenCommiting();
		this.hashProvider = hashProvider;
		this.defaultValue = defaultValue;
		this.nodeCache = nodeCache;
	}

	public VersionedMapStoreImpl(ContinousHashProvider<K> hashProvider, V defaultValue) {
		this(hashProvider, defaultValue, new VersionedMapStoreConfiguration());
	}

	public static <K, V> List<VersionedMapStore<K, V>> createSharedVersionedMapStores(int amount,
			ContinousHashProvider<K> hashProvider, V defaultValue,
			VersionedMapStoreConfiguration config) {
		List<VersionedMapStore<K, V>> result = new ArrayList<>(amount);
		if (config.isSharedNodeCacheInStoreGroups()) {
			Map<Node<K, V>, ImmutableNode<K, V>> nodeCache;
			if (config.isSharedNodeCacheInStore()) {
				nodeCache = createNodeCache();
			} else {
				nodeCache = null;
			}
			for (int i = 0; i < amount; i++) {
				result.add(new VersionedMapStoreImpl<>(hashProvider, defaultValue, nodeCache, config));
			}
		} else {
			for (int i = 0; i < amount; i++) {
				result.add(new VersionedMapStoreImpl<>(hashProvider, defaultValue, config));
			}
		}
		return result;
	}
	
	private static <K,V> Map<Node<K, V>, ImmutableNode<K, V>> createNodeCache() {
		return new HashMap<>();
	}
	
	public static <K, V> List<VersionedMapStore<K, V>> createSharedVersionedMapStores(int amount,
			ContinousHashProvider<K> hashProvider, V defaultValue) {
		return createSharedVersionedMapStores(amount, hashProvider, defaultValue, new VersionedMapStoreConfiguration());
	}
	
	@Override
	public synchronized MutableLongSet getStates() {
		return this.states.keySet();
	}

	@Override
	public VersionedMap<K, V> createMap() {
		return new VersionedMapImpl<>(this, hashProvider, defaultValue);
	}

	@Override
	public VersionedMap<K, V> createMap(long state) {
		ImmutableNode<K, V> data = revert(state);
		return new VersionedMapImpl<>(this, hashProvider, defaultValue, data);
	}
	

	public synchronized ImmutableNode<K, V> revert(long state) {
		if (states.containsKey(state)) {
			return states.get(state);
		} else {
			throw new IllegalArgumentException("Store does not contain state " + state + "! Avaliable states: "
					+ Arrays.toString(states.toArray()));
		}
	}

	public synchronized long commit(Node<K, V> data, VersionedMapImpl<K, V> mapToUpdateRoot) {
		ImmutableNode<K, V> immutable;
		if (data != null) {
			immutable = data.toImmutable(this.nodeCache);
		} else {
			immutable = null;
		}

		if (nextID == Long.MAX_VALUE)
			throw new IllegalStateException("Map store run out of Id-s");
		long id = nextID++;
		this.states.put(id, immutable);
		if (this.immutableWhenCommiting) {
			mapToUpdateRoot.setRoot(immutable);
		}
		return id;
	}
	
	@Override
	public DiffCursor<K, V> getDiffCursor(long fromState, long toState) {
		VersionedMap<K, V> map1 = createMap(fromState);
		VersionedMap<K, V> map2 = createMap(toState);
		Cursor<K, V> cursor1 = map1.getAll();
		Cursor<K, V> cursor2 = map2.getAll();
		return new MapDiffCursor<>(this.hashProvider, this.defaultValue, cursor1, cursor2);
	}
	
	@Override
	public VersionedMapStoreStatistics getStatistics(Set<VersionedMapStoreStatistics> existingStatistics) {
		for (VersionedMapStoreStatistics existing : existingStatistics) {
			if(existing.getNodeCache() == nodeCache) {
				return existing;
			}
		}
		int noStates = this.states.size();
		VersionedMapStatistics mapStatistics = new VersionedMapStatistics();
		if(nodeCache != null) {
			for (Entry<Node<K, V>, ImmutableNode<K, V>> entry : this.nodeCache.entrySet()) {
				entry.getValue().fillStatistics(mapStatistics, 0, false);
			}
		}
		return new VersionedMapStoreStatistics(noStates, nodeCache, mapStatistics);
	}
}
