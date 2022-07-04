package tools.refinery.store.map.internal;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import tools.refinery.store.map.ContinousHashProvider;
import tools.refinery.store.map.Cursor;
import tools.refinery.store.map.DiffCursor;
import tools.refinery.store.map.VersionedMap;
import tools.refinery.store.map.VersionedMapStatistics;
import tools.refinery.store.map.VersionedMapStoreImpl;

/**
 * Not threadSafe in itself
 * @author Oszkar Semerath
 *
 * @param <K>
 * @param <V>
 */
public class VersionedMapImpl<K,V> implements VersionedMap<K,V>{
	protected final VersionedMapStoreImpl<K,V> store;
	
	protected final ContinousHashProvider<K> hashProvider;
	protected final V defaultValue;
	protected Node<K,V> root;
	
	private OldValueBox<V> oldValueBox = new OldValueBox<>();
	
	public VersionedMapImpl(
			VersionedMapStoreImpl<K,V> store,
			ContinousHashProvider<K> hashProvider,
			V defaultValue)
	{
		this.store = store;
		this.hashProvider = hashProvider;
		this.defaultValue = defaultValue;
		this.root = null;
	}
	public VersionedMapImpl(
			VersionedMapStoreImpl<K,V> store,
			ContinousHashProvider<K> hashProvider,
			V defaultValue, Node<K,V> data)
	{
		this.store = store;
		this.hashProvider = hashProvider;
		this.defaultValue = defaultValue;
		this.root = data;
	}
		
	public V getDefaultValue() {
		return defaultValue;
	}
	public ContinousHashProvider<K> getHashProvider() {
		return hashProvider;
	}
	@Override
	public V put(K key, V value) {
		if(root!=null) {
			root = root.putValue(key, value, oldValueBox, hashProvider, defaultValue, hashProvider.getHash(key, 0), 0);
			return oldValueBox.getOldValue();
		} else {
			root = MutableNode.initialize(key, value, hashProvider, defaultValue);
			return defaultValue;
		}
	}
	
	@Override
	public void putAll(Cursor<K, V> cursor) {
		if(cursor.getDependingMaps().contains(this)) {
			List<K> keys = new LinkedList<>();
			List<V> values = new LinkedList<>();
			while(cursor.move()) {
				keys.add(cursor.getKey());
				values.add(cursor.getValue());
			}
			Iterator<K> keyIterator = keys.iterator();
			Iterator<V> valueIterator = values.iterator();
			while(keyIterator.hasNext()) {
				this.put(keyIterator.next(), valueIterator.next());
			}
		} else {
			while(cursor.move()) {
				this.put(cursor.getKey(), cursor.getValue());
			}
		}
	}
	
	@Override
	public V get(K key) {
		if(root!=null) {
			return root.getValue(key, hashProvider, defaultValue, hashProvider.getHash(key, 0), 0);
		} else {
			return defaultValue;
		}
	}
	@Override
	public long getSize() {
		if(root == null) {
			return 0;
		} else {
			return root.getSize();
		}
	}

	@Override
	public Cursor<K, V> getAll() {
		return new MapCursor<>(this.root,this);
	}
	@Override
	public DiffCursor<K, V> getDiffCursor(long toVersion) {
		Cursor<K, V> fromCursor = this.getAll();
		VersionedMap<K, V> toMap = this.store.createMap(toVersion);
		Cursor<K, V> toCursor = toMap.getAll();
		return new MapDiffCursor<>(this.hashProvider,this.defaultValue, fromCursor, toCursor);
		
	}
	

	@Override
	public long commit() {
		return this.store.commit(root,this);
	}
	public void setRoot(Node<K, V> root) {
		this.root = root;
	}

	@Override
	public void restore(long state) {
		root = this.store.revert(state);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((root == null) ? 0 : root.hashCode());
		return result;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		VersionedMapImpl<?,?> other = (VersionedMapImpl<?,?>) obj;
		if (root == null) {
			if (other.root != null)
				return false;
		} else if (!root.equals(other.root))
			return false;
		return true;
	}
	public void prettyPrint() {
		StringBuilder s = new StringBuilder();
		if(this.root != null) {
			this.root.prettyPrint(s, 0, -1);
			System.out.println(s.toString());
		} else {
			System.out.println("empty tree");
		}
	}
	public void checkIntegrity() {
		if(this.root != null) {
			this.root.checkIntegrity(hashProvider, defaultValue, 0);
		}
	}
	
	@Override
	public VersionedMapStatistics getStatistics() {
		VersionedMapStatistics statistics = new VersionedMapStatistics();
		if(this.root != null) {
			root.fillStatistics(statistics, 0, true);
		}
		return statistics;
	}
}
